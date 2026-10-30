#!/usr/bin/env python3
"""Local MSC/Lean atlas. Explicit research runs may send supplied context to Codex."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
import re
import threading
import traceback
from urllib.parse import urlsplit, unquote, parse_qs
import uuid

import analysis_engine
import lean_service

ROOT=Path(__file__).resolve().parent
RUNS=ROOT/'runs'
MAX_BODY=5*1024*1024
EXECUTOR=ThreadPoolExecutor(max_workers=1,thread_name_prefix='lean-atlas')
JOBS={}
LOCK=threading.Lock()
RESEARCH=None

def research():
    global RESEARCH
    if RESEARCH is None:
        from research_service import ResearchService
        with LOCK:
            if RESEARCH is None: RESEARCH=ResearchService()
    return RESEARCH

def now(): return datetime.now(timezone.utc).isoformat()

def save(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    temporary=path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value,ensure_ascii=False,indent=2,default=str)+'\n')
    temporary.replace(path)

def dataset(): return json.loads((ROOT/'data/msc2020.json').read_text())

def safe_id(value):
    if not isinstance(value,str) or not re.fullmatch(r'[a-f0-9]{32}',value): raise ValueError('Недопустимый ID исследования.')
    return value

def normalized_inputs(payload):
    files=payload.get('files')
    if not isinstance(files,list) or len(files)!=2: raise ValueError('Нужны ровно два Lean-файла.')
    out=[]
    for item in files:
        if not isinstance(item,dict): raise ValueError('Неверный формат файла.')
        name=item.get('name');content=item.get('content')
        if not isinstance(name,str) or not name.endswith('.lean') or len(name)>240: raise ValueError('Нужно имя файла с расширением .lean.')
        p=Path(name)
        if p.is_absolute() or any(part in ('..','.') for part in p.parts) or '\\' in name or '\x00' in name: raise ValueError('Имя файла должно быть безопасным относительным путём.')
        if not isinstance(content,str) or not content.strip() or len(content.encode())>2*1024*1024: raise ValueError('Файл пуст или превышает 2 МБ.')
        out.append(dict(name=name,content=content))
    if out[0]['name']==out[1]['name']: raise ValueError('Имена двух модулей должны различаться.')
    context=payload.get('context',{})
    if not isinstance(context,dict): raise ValueError('Контекст должен быть объектом.')
    allowed={'project_root','lean','mathlib'}
    context={k:v.strip() for k,v in context.items() if k in allowed and isinstance(v,str) and (v.strip() or k!='lean')}
    targets=payload.get('targets',['',''])
    if not isinstance(targets,list) or len(targets)!=2 or not all(isinstance(x,str) and len(x)<500 for x in targets): raise ValueError('Нужны два имени целевых деклараций либо пустые строки.')
    overrides=payload.get('msc_overrides',[[],[]])
    if not isinstance(overrides,list) or len(overrides)!=2: raise ValueError('Неверный формат MSC-меток.')
    known={n['id'] for n in dataset()['nodes']}
    for codes in overrides:
        if not isinstance(codes,list) or len(codes)>12 or not all(isinstance(c,str) for c in codes):
            raise ValueError('Для каждого объекта нужен список не более 12 строковых MSC-кодов.')
        if any(c not in known for c in codes): raise ValueError('Неизвестный MSC-код: '+', '.join(c for c in codes if c not in known))
    return out,context,targets,overrides

def run_analysis(payload,run_id=None,progress=None):
    files,context,targets,overrides=normalized_inputs(payload)
    run_id=run_id or uuid.uuid4().hex
    folder=RUNS/safe_id(run_id)
    folder.mkdir(parents=True,exist_ok=True)
    save(folder/'input.json',dict(files=files,context=context,targets=targets,msc_overrides=overrides,created_at=now()))
    if progress: progress('Lean читает два модуля и извлекает определения и зависимости.')
    inspection=lean_service.inspect_files(files,context,folder/'inspection')
    save(folder/'inspection.json',inspection)
    if progress: progress('Подбираются MSC-метки, маршруты навигации и кандидаты связи.')
    result=analysis_engine.assemble_analysis(run_id,files,inspection,dataset(),targets,overrides,lean_service.load_examples())
    result.update(created_at=now(),verification=None)
    save(folder/'analysis.json',result)
    return result

def run_verification(payload,progress=None):
    run_id=safe_id(payload.get('analysis_id'))
    folder=RUNS/run_id
    source=payload.get('bridge_source');targets=payload.get('bridge_targets')
    if not isinstance(source,str) or not source.strip() or len(source.encode())>1024*1024: raise ValueError('Нужен непустой Lean-текст моста размером до 1 МБ.')
    if not isinstance(targets,list) or not targets or len(targets)>20 or not all(isinstance(x,str) and 0<len(x)<500 for x in targets): raise ValueError('Укажите имена 1–20 проверяемых теорем.')
    report=json.loads((folder/'analysis.json').read_text())
    inputs=json.loads((folder/'input.json').read_text())
    inspection=json.loads((folder/'inspection.json').read_text())
    inspection['selected_targets']=inputs.get('targets',['',''])
    verification_id=uuid.uuid4().hex
    work=folder/'verifications'/verification_id
    work.mkdir(parents=True,exist_ok=True)
    # Invalidate previous success before attempting the new proof.
    report['verification']=dict(status='running',success=False,verification_id=verification_id,started_at=now())
    report['bridge_source']=source
    report['bridge_targets']=targets
    save(folder/'analysis.json',report)
    if progress: progress('Lean заново проверяет входы, связующую теорему и её зависимости.')
    try:
        result=lean_service.verify_bridge(source,targets,inputs['context'],work,inspection=inspection)
    except Exception as error:
        result=dict(status='failed',success=False,diagnostics=[str(error)],checked_at=now())
    result.update(analysis_id=run_id,verification_id=verification_id)
    save(work/'result.json',result)
    report['verification']=result
    save(folder/'analysis.json',report)
    return result

def submit(kind,payload):
    job_id=uuid.uuid4().hex
    state=dict(id=job_id,status='queued',progress='Задача в очереди',created_at=now())
    with LOCK: JOBS[job_id]=state
    def progress(message):
        with LOCK: JOBS[job_id]['progress']=message
    def work():
        with LOCK: JOBS[job_id].update(status='running',progress='Выполняется')
        try:
            value=run_analysis(payload,progress=progress) if kind=='analyze' else run_verification(payload,progress=progress)
            with LOCK: JOBS[job_id].update(status='complete',progress='Готово',result=value,finished_at=now())
        except Exception as error:
            with LOCK: JOBS[job_id].update(status='failed',progress='Не удалось завершить',error=str(error),finished_at=now())
            traceback.print_exc()
    EXECUTOR.submit(work)
    return dict(job_id=job_id)

class Handler(BaseHTTPRequestHandler):
    server_version='MSCLeanAtlas/0.1'

    def local_host(self):
        return self.headers.get('Host','') in {'127.0.0.1:'+str(self.server.server_port),'localhost:'+str(self.server.server_port)}

    def json_response(self,value,status=200):
        body=json.dumps(value,ensure_ascii=False,default=str).encode()
        self.send_response(status);self.send_header('Content-Type','application/json; charset=utf-8')
        self.send_header('Content-Length',str(len(body)));self.send_header('Cache-Control','no-store')
        self.send_header('X-Content-Type-Options','nosniff');self.end_headers();self.wfile.write(body)

    def do_GET(self):
        try:
            if not self.local_host(): return self.json_response({'error':'Этот сервис доступен только через localhost.'},403)
            path=urlsplit(self.path).path
            if path=='/api/research/status': return self.json_response(research().status())
            if path=='/api/research/cases': return self.json_response({'cases':research().cases()})
            if path=='/api/research/runs': return self.json_response({'runs':research().list_runs()})
            if path=='/api/research/search':
                import research_retrieval
                query=parse_qs(urlsplit(self.path).query).get('q',[''])[0]
                return self.json_response({'results':research_retrieval.search(query,research().cases())})
            if path.startswith('/api/research/runs/'):
                parts=path.split('/')
                if len(parts)>6 and parts[5]=='artifacts':
                    file=research().artifact(parts[4],unquote('/'.join(parts[6:])))
                    body=file.read_bytes();self.send_response(200)
                    self.send_header('Content-Type','text/plain; charset=utf-8')
                    self.send_header('Content-Length',str(len(body)))
                    self.send_header('X-Content-Type-Options','nosniff')
                    self.end_headers();self.wfile.write(body);return
                if len(parts)==5: return self.json_response(research().get(parts[4]))
                return self.json_response({'error':'Не найдено'},404)
            if path=='/api/graph': return self.json_response(dataset())
            if path=='/api/examples': return self.json_response(lean_service.load_examples())
            if path=='/api/status':
                data=dataset();context=lean_service.default_context()
                return self.json_response(dict(ready=True,context=context,data=data['meta'],
                    capabilities={'full_msc':True,'local_search':True,'lean_verification':True,'generative_model':True,
                                  'codex_research':True,'lemma_dag':True,'universal_bridge_discovery':False}))
            if path.startswith('/api/jobs/'):
                key=safe_id(path.rsplit('/',1)[1])
                with LOCK: job=dict(JOBS[key]) if key in JOBS else None
                return self.json_response(job or {'error':'Задача не найдена'},200 if job else 404)
            if path.startswith('/api/runs/'):
                key=safe_id(path.rsplit('/',1)[1]);file=RUNS/key/'analysis.json'
                if not file.exists(): return self.json_response({'error':'Исследование не найдено'},404)
                result=json.loads(file.read_text())
                result['input']=json.loads((RUNS/key/'input.json').read_text())
                return self.json_response(result)
            file=(ROOT/'web'/unquote(path.lstrip('/') or 'index.html')).resolve()
            if not file.is_relative_to((ROOT/'web').resolve()) or not file.is_file(): return self.json_response({'error':'Не найдено'},404)
            types={'.html':'text/html; charset=utf-8','.js':'application/javascript; charset=utf-8','.css':'text/css; charset=utf-8','.svg':'image/svg+xml'}
            body=file.read_bytes();self.send_response(200);self.send_header('Content-Type',types.get(file.suffix,'application/octet-stream'))
            self.send_header('Content-Length',str(len(body)));self.send_header('X-Content-Type-Options','nosniff')
            self.send_header('Content-Security-Policy',"default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'self'; base-uri 'none'; frame-ancestors 'none'")
            self.end_headers();self.wfile.write(body)
        except FileNotFoundError as error: self.json_response({'error':str(error)},404)
        except (ValueError,KeyError) as error: self.json_response({'error':str(error)},400)
        except BrokenPipeError: pass
        except Exception as error: traceback.print_exc();self.json_response({'error':str(error)},500)

    def do_POST(self):
        try:
            host=self.headers.get('Host','')
            if not self.local_host():
                return self.json_response({'error':'Этот сервис доступен только через localhost.'},403)
            origin=self.headers.get('Origin')
            if origin and origin not in {'http://'+host}: return self.json_response({'error':'Запрос должен исходить из локального приложения.'},403)
            if not self.headers.get('Content-Type','').startswith('application/json'): return self.json_response({'error':'Нужен Content-Type application/json.'},415)
            length=int(self.headers.get('Content-Length','0'))
            if length<1 or length>MAX_BODY: return self.json_response({'error':'Размер запроса вне допустимого диапазона.'},413)
            payload=json.loads(self.rfile.read(length))
            if not isinstance(payload,dict): raise ValueError('Тело запроса должно быть JSON-объектом.')
            path=urlsplit(self.path).path
            if path=='/api/research/runs': return self.json_response(research().create(payload),202)
            if path.startswith('/api/research/runs/'):
                parts=path.split('/')
                if len(parts)==6 and parts[5]=='cancel': return self.json_response(research().cancel(parts[4]))
                if len(parts)==6 and parts[5]=='resume': return self.json_response(research().start(parts[4]),202)
                return self.json_response({'error':'Не найдено'},404)
            if path=='/api/analyze': normalized_inputs(payload);return self.json_response(submit('analyze',payload),202)
            if path=='/api/verify': safe_id(payload.get('analysis_id'));return self.json_response(submit('verify',payload),202)
            return self.json_response({'error':'Не найдено'},404)
        except FileNotFoundError as error: self.json_response({'error':str(error)},404)
        except (ValueError,TypeError) as error: self.json_response({'error':str(error)},400)
        except Exception as error: traceback.print_exc();self.json_response({'error':str(error)},500)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--port',type=int,default=8765);args=p.parse_args()
    if not (ROOT/'data/msc2020.json').exists(): raise SystemExit('Сначала запустите python3 import_msc.py')
    server=ThreadingHTTPServer(('127.0.0.1',args.port),Handler)
    print(f'MSC × Lean: http://127.0.0.1:{server.server_port}',flush=True)
    try: server.serve_forever()
    except KeyboardInterrupt: pass
    finally:
        server.server_close();EXECUTOR.shutdown(wait=False,cancel_futures=True)
        if RESEARCH:
            for flag in RESEARCH.cancel_flags.values(): flag.set()
            RESEARCH.pool.shutdown(wait=False,cancel_futures=True)

if __name__=='__main__': main()
