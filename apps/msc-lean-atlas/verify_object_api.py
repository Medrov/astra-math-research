"""Exercise the real local object workflow. Model inference is explicitly opt-in."""
import argparse
import copy
from datetime import datetime, timezone
import json
from pathlib import Path
import time
from urllib.error import HTTPError
from urllib.request import Request, urlopen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', default='http://127.0.0.1:8766')
    parser.add_argument('--with-model', action='store_true')
    args = parser.parse_args()
    report = dict(checked_at=datetime.now(timezone.utc).isoformat(), base=args.base, mocked=False,
                  model_inference_requested=args.with_model, checks=[], runs=[])
    output = Path(__file__).resolve().parent / 'verification' / 'object-api-report.json'
    output.parent.mkdir(exist_ok=True)

    def save():
        output.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')

    def api(path, data=None, expected=200):
        request = Request(args.base+path, data=json.dumps(data,ensure_ascii=False).encode() if data is not None else None,
                          headers={'Content-Type':'application/json'})
        try:
            with urlopen(request,timeout=40) as response:
                status,value=response.status,json.load(response)
        except HTTPError as error:
            status,value=error.code,json.load(error)
        assert status==expected, (path,status,value)
        return value

    def wait(run, timeout=660):
        started=time.monotonic()
        while time.monotonic()-started<timeout:
            value=api('/api/research/runs/'+run['id'])
            if value['status'] not in ('queued','running'):
                report['runs'].append(dict(id=value['id'],mode=value['mode'],purpose=value.get('purpose'),
                                           status=value['status'],outcome=value['outcome'],usage=value['usage'],
                                           graph_ref=value.get('graph_ref'),error=value.get('error')))
                save()
                return value
            time.sleep(1)
        raise TimeoutError('Run did not finish: '+run['id'])

    def check(name, fn):
        print('CHECK '+name,flush=True)
        try:
            detail=fn()
            report['checks'].append(dict(name=name,passed=True,evidence=detail))
            print('PASS '+name,flush=True)
            return detail
        except Exception as error:
            report['checks'].append(dict(name=name,passed=False,error=str(error)))
            print('FAIL '+name+': '+str(error),flush=True)
            raise
        finally:
            save()

    def run_case(case, transition=None, mode='pilot'):
        payload=dict(case_id=case,mode=mode,budget={'max_calls':6 if mode!='pilot' else 0,'timeout_seconds':600})
        if transition: payload['transition_id']=transition
        run=wait(api('/api/research/runs',payload,202))
        assert run['status']=='complete', run.get('error')
        selected=next(t for t in run['object_graph']['transitions'] if t['id']==run['selected_transition_id'])
        expected='refuted' if case=='graph_energy_negative' and transition!='energy_identity' else 'proved'
        assert selected['status']==expected,(selected['status'],selected.get('last_result'))
        assert selected['certificate']
        assert all(o['ok'] for o in selected['certificate']['result']['verification']['obligations'])
        return run

    try:
        cases=api('/api/research/cases')['cases']
        check('Cases expose explicit object graphs',lambda: {'cases':len(cases),'all_have_graphs':all(c.get('object_graph') for c in cases)} if all(c.get('object_graph') for c in cases) else (_ for _ in ()).throw(AssertionError('Missing graph')))
        positive=check('Positive transfer certifies every obligation',lambda: run_case('graph_energy'))
        check('Preview identity selection stays independent',lambda: run_case('graph_energy','energy_identity'))
        check('Negative weight refutes unconditional positivity',lambda: run_case('graph_energy_negative'))
        graph=positive['object_graph']

        def revise():
            current=api('/api/objects/graphs/'+graph['id'])
            # Re-running this check preserves history and restores the exact original contract first.
            if current['revision']!=graph['revision']:
                current=api('/api/objects/graphs/'+graph['id']+'/revisions',{'graph':copy.deepcopy(graph),'expected_revision':current['revision']},201)
            metadata=copy.deepcopy(current); metadata['title']+=' — проверка представления'
            renamed=api('/api/objects/graphs/'+graph['id']+'/revisions',{'graph':metadata,'expected_revision':current['revision']},201)
            selected=next(t for t in renamed['transitions'] if t['id']==positive['selected_transition_id'])
            assert selected['status']=='proved'
            semantic=copy.deepcopy(renamed); semantic['objects'][0]['definition']+=' Изменённая постановка для проверки версий.'
            changed=api('/api/objects/graphs/'+graph['id']+'/revisions',{'graph':semantic,'expected_revision':renamed['revision']},201)
            selected=next(t for t in changed['transitions'] if t['id']==positive['selected_transition_id'])
            assert selected['status']=='needs_recheck' and not selected['certificate']
            api('/api/research/runs',dict(mode='pilot',graph_id=changed['id'],graph_revision=changed['revision'],transition_id=selected['id']),400)
            historical=api('/api/objects/graphs/'+graph['id']+'?revision='+str(graph['revision']))
            assert next(t for t in historical['transitions'] if t['id']==selected['id'])['status']=='proved'
            return {'graph_id':graph['id'],'original_revision':graph['revision'],'changed_revision':changed['revision'],'historical_certificate_preserved':True}
        check('Metadata reuse, semantic invalidation and historical certificate',revise)

        def resume():
            run=api('/api/research/runs',dict(case_id='graph_energy_negative',mode='pilot'),202)
            api('/api/research/runs/'+run['id']+'/cancel',{})
            stopped=wait(run)
            if stopped['status']!='complete':
                assert stopped['status']=='cancelled',stopped
                stopped=wait(api('/api/research/runs/'+run['id']+'/resume',{},202))
            assert stopped['status']=='complete' and stopped['outcome']=='refuted',stopped.get('error')
            assert stopped['usage']['calls']==0
            return {'run_id':run['id'],'status':stopped['status'],'model_calls':0}
        check('Cancel and resume preserve a local run',resume)

        if args.with_model:
            real=check('Real Astra graph planning and Lean certification',lambda: run_case('graph_energy',mode='single'))
            assert real['usage']['calls']>0
            assert real['semantic_review']['status']=='aligned',real['semantic_review']

            def discover():
                run=wait(api('/api/research/runs',dict(purpose='discover',mode='single',msc_codes=['05C50','15A63'],
                    question='Предложите две простые проверяемые связи для явной координатной модели взвешенного треугольника: энергия, квадратичная форма и неотрицательность. Используйте небольшие Lean-формулировки и определения, чтобы выбранную связь можно было проверить отдельно.',
                    budget={'max_calls':2,'timeout_seconds':600}),202))
                assert run['status']=='complete',run.get('error')
                assert 1<=len(run['object_graph']['transitions'])<=3
                assert all(t['status']=='proposed' and not t['certificate'] for t in run['object_graph']['transitions'])
                return run
            candidates=check('Real Astra proposes candidates without claiming proof',discover)
            # Verify one actual proposed task using the same user path as the UI.
            candidate=candidates['object_graph']['transitions'][0]
            def prove_candidate():
                run=wait(api('/api/research/runs',dict(purpose='prove',mode='single',graph_id=candidates['graph_ref']['id'],
                    graph_revision=candidates['graph_ref']['revision'],transition_id=candidate['id'],
                    budget={'max_calls':8,'timeout_seconds':600}),202))
                assert run['status']=='complete',run.get('error')
                selected=next(t for t in run['object_graph']['transitions'] if t['id']==candidate['id'])
                assert selected['status']=='proved', (run.get('result'),run.get('contract_review'),selected.get('last_result'))
                assert run['semantic_review']['status']=='aligned',run['semantic_review']
                return run
            check('Selected proposed transition is formalized and certified',prove_candidate)
        report['passed']=all(item['passed'] for item in report['checks'])
    except Exception:
        report['passed']=False
        raise
    finally:
        save()
        print(json.dumps({'passed':report.get('passed'),'checks':len(report['checks']),'report':str(output)},ensure_ascii=False),flush=True)


if __name__=='__main__':
    main()
