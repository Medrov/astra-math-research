"""Conservative, local retrieval. Scores are rankings, never truth probabilities."""
from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
STOP = set('theory general other with without under over from into that this their its and for the are all any one two let def theorem lemma have show exact import namespace end variable variables type prop sorts sort instances instance class structure set fun by of in to at as on is a an'.split())
GENERIC = {'Eq','HEq','Nat','Int','Rat','Real','Bool','True','False','And','Or','Not','Iff','Exists','Forall','Function','OfNat','HAdd','HMul','HSub','HDiv','LT','LE','Decidable','Nonempty','Classical','List','Option','Unit','Prod','Fin','Set','Subtype'}
RULES = [
 ('05', ['laplacian','graph','incidence','fano','combinatorics','simplegraph'], 'Графовые и комбинаторные конструкции'),
 ('06', ['closureoperator','galoisconnection','galoisinsertion','orderhom','orderiso','lattice','semilattice','preorder'], 'Порядок, решётки и общие замыкания'),
 ('11', ['prime','coprime','divisibility','numbertheory','zmod'], 'Арифметические конструкции'),
 ('13', ['ideal','commring','localization','polynomial','commutative'], 'Коммутативные кольца и модули'),
 ('14', ['scheme','affine','spectrum','algebraicgeometry'], 'Алгебраическая геометрия'),
 ('15', ['linear','matrix','quadratic','submodule','bilinear','linearalgebra','dotproduct'], 'Линейная и матричная структура'),
 ('16', ['quiver','representation','associative','module'], 'Ассоциативные алгебры и представления'),
 ('17', ['octonion','associator','nonassociative','jordan','albert','cayley'], 'Неассоциативные алгебры'),
 ('18', ['category','functor','naturalisomorphism','adjunction'], 'Категорные конструкции'),
 ('20', ['subgroup','group','groupaction','grouphom','mulhom'], 'Группы и подгруппы'),
 ('49', ['totalvariation','variational','variation'], 'Вариационные конструкции'),
 ('52', ['convex','convexhull','polytope','polyhedron'], 'Выпуклая и дискретная геометрия'),
 ('54', ['topologicalspace','topology','isclosed','isopen','continuous'], 'Топологическая структура'),
 ('55', ['homology','homotopy','persistence','persistent','simplicial'], 'Алгебраическая топология'),
 ('60', ['markov','probability','measuretheory','random','stochastic'], 'Вероятностные конструкции'),
 ('90', ['submodular','optimization','minimization','maxflow','linearprogram'], 'Оптимизация'),
 ('94', ['hamming','codeword','coding','probes','oneerror','decoder'], 'Кодирование и ошибки'),
]

def tokens(text):
    text = re.sub(r'([a-z])([A-Z])', r'\1 \2', text)
    return [x.lower() for x in re.findall(r'[A-Za-z][A-Za-z0-9]*', text) if len(x)>2 and x.lower() not in STOP]

def declaration_text(declarations):
    return '\n'.join(str(d.get('name',''))+' '+str(d.get('type',''))+' '+' '.join(d.get('dependencies',[])) for d in declarations)

def classify(source, declarations, dataset, overrides=None):
    by_id={n['id']:n for n in dataset['nodes']}
    if overrides:
        if not isinstance(overrides,list) or len(overrides)>12: raise ValueError('Укажите не более 12 MSC-кодов для каждого объекта.')
        unknown=[c for c in overrides if c not in by_id]
        if unknown: raise ValueError('MSC-коды отсутствуют в выгрузке: '+', '.join(unknown))
        return [dict(code=c,title=by_id[c]['title'],score=None,evidence=['Метка задана пользователем; это тематическая привязка, не математическое доказательство.'],status='user_confirmed') for c in dict.fromkeys(overrides)]
    resolved=declaration_text(declarations)
    vocabulary=set(tokens(resolved))
    # Full source adds lexical clues, including comments; never gives a verified tag.
    source_vocab=set(tokens(source))
    # Imported namespace names are not the object's mathematical structure.
    # E.g. a graph operator housed in an Albert namespace remains a graph clue.
    rule_parts=[]
    meaningful_qualifiers={'Subgroup','Submodule','SimpleGraph','LinearMap','OrderHom','ClosureOperator','TopologicalSpace'}
    for declaration in declarations:
        rule_parts.extend([declaration.get('name','').rsplit('.',1)[-1],str(declaration.get('type',''))])
        for dep in declaration.get('dependencies',[]):
            pieces=dep.split('.')
            rule_parts.append(pieces[-1])
            rule_parts.extend(x for x in pieces[:-1] if x in meaningful_qualifiers)
    compact=re.sub(r'[^a-z0-9]','', ' '.join(rule_parts).lower())
    source_compact=re.sub(r'[^a-z0-9]','',source[:300000].lower())
    ranked={}
    for code,terms,label in RULES:
        hits=[t for t in terms if t in compact]
        weak=[t for t in terms if t not in hits and t in source_compact]
        if (hits or weak) and code in by_id:
            ranked[code]=(8*len(hits)+2*len(weak),[label+': '+', '.join(hits+weak), 'Эвристика по именам/типам/тексту; проверьте тематическую метку.'])
    frequency=Counter(t for n in dataset['nodes'] for t in set(tokens(n['title'])))
    for n in dataset['nodes']:
        if n['level']==0: continue
        terms=set(tokens(n['title']))
        overlap=terms&vocabulary
        weak=(terms&source_vocab)-overlap
        # Require two title terms, or a distinctive term explicitly in a declaration.
        if len(overlap|weak)<2 and not any(frequency[t]<=12 for t in overlap): continue
        score=sum(4/(1+frequency[t]/30) for t in overlap)+sum(1/(1+frequency[t]/30) for t in weak)
        if score>=2.5:
            ranked[n['id']]=(round(score,3),['Совпавшие термины рубрики: '+', '.join(sorted(overlap|weak)), 'Текстовый поиск; соответствие рубрике не подтверждено.'])
    candidates=sorted(ranked,key=lambda c:(-ranked[c][0],c))
    # Retain coarse anchors plus useful detailed suggestions, at most eight.
    selected=candidates[:8]
    return [dict(code=c,title=by_id[c]['title'],score=ranked[c][0],evidence=ranked[c][1],status='suggested') for c in selected]

def navigation_path(source,target,dataset):
    adjacency={n['id']:[] for n in dataset['nodes']}
    endpoints={source,target}
    def transit_allowed(code):
        # Publication-format/history hubs connect almost everything but add no
        # subject-specific orientation. They remain in the full dataset/UI.
        if code in endpoints: return True
        if '-' in code: return False
        if code[:2] in {'00','01'} and code[:2] not in {source[:2],target[:2]}: return False
        return True
    for e in dataset['edges']:
        if e['source'] not in adjacency or e['target'] not in adjacency: continue
        if not transit_allowed(e['source']) or not transit_allowed(e['target']): continue
        if e['type']=='broader':
            adjacency[e['source']].append((e['target'],'broader'))
            adjacency[e['target']].append((e['source'],'narrower'))
        elif e['type']=='see_also': adjacency[e['source']].append((e['target'],'see_also'))
    previous={source:None}; queue=deque([source])
    while queue:
        node=queue.popleft()
        if node==target: break
        for nxt,kind in adjacency.get(node,[]):
            if nxt not in previous: previous[nxt]=(node,kind);queue.append(nxt)
    out=dict(source=source,target=target,status='navigation_only',nodes=[],edge_types=[],
             search_policy='subject_navigation_v2',
             transit_filter='Служебные рубрики с дефисом и общие исторические/метатематические разделы не используются как транзитные узлы; выбранные конечные рубрики сохраняются.')
    if target not in previous:
        out['explanation']='В импортированной иерархии и отсылках see_also путь не найден. Это не доказывает отсутствия математической связи.'
        return out
    n=target;path=[n];types=[]
    while previous[n] is not None:
        p,k=previous[n];path.append(p);types.append(k);n=p
    out.update(nodes=list(reversed(path)),edge_types=list(reversed(types)),explanation='Тематический маршрут по классификатору без транзита через служебные рубрики. Он не задаёт математическое отображение или доказательство связи объектов.')
    return out

def meaningful_dependencies(declarations):
    out=set()
    for d in declarations:
        for name in d.get('dependencies',[]):
            if name.split('.')[0] in GENERIC or name.startswith(('Lean.','_private.','inst','IO.','String.')): continue
            if len(name)>3: out.add(name)
    return out

def structural_candidates(left,right):
    a,b=left['selected_declarations'],right['selected_declarations']
    shared=sorted(meaningful_dependencies(a)&meaningful_dependencies(b))
    candidates=[]
    if shared:
        candidates.append(dict(id='shared-declarations',title='Общие формальные зависимости',status='candidate',kind='shared_dependency',
          explanation='Оба выбранных объекта используют перечисленные декларации. Это точное совпадение зависимостей, но ещё не отображение между объектами.',
          evidence=shared[:30],source_declarations=[d['name'] for d in a],target_declarations=[d['name'] for d in b],
          requirements=['Определить, что именно сохраняется при предполагаемом соответствии.','Сформулировать отдельную связующую теорему.']))
    for da in a[:12]:
        for db in b[:12]:
            ta=re.sub(r'\s+',' ',str(da.get('type',''))).strip()
            tb=re.sub(r'\s+',' ',str(db.get('type',''))).strip()
            if ta and ta==tb and len(ta)>6:
                candidates.append(dict(id='shared-type',title='Совпадающие отображённые типы',status='candidate',kind='same_printed_type',
                  explanation='Отображённые компилятором типы совпали. Это повод проверить равенство или сохранение структуры; совпадение текста типов не доказывает равенство объектов.',
                  evidence=[da['name']+' : '+ta,db['name']+' : '+tb],requirements=['Проверить типы в общем Lean-окружении.','Доказать предложенное отношение.']))
                return candidates,shared
    return candidates,shared

def catalog_candidates(left,right):
    catalog=json.loads((ROOT/'catalog/bridges.json').read_text())['edges']
    majors=lambda f:{m['code'][:2] for m in f['msc_matches']}
    a,b=majors(left),majors(right)
    out=[]
    for e in catalog:
        if not ((a&set(e['source_msc']) and b&set(e['target_msc'])) or (b&set(e['source_msc']) and a&set(e['target_msc']))): continue
        out.append(dict(id='literature-'+e['id'],title=e['label'],status='candidate',kind='literature_lead',evidence_status=e['verification'],
          application_status='unverified',explanation=e['claim']+' Применимость к загруженным объектам ещё не установлена.',
          evidence=[e['source_title'],e['locator']],source_url=e['source_url'],requirements=e['assumptions']+[e['caveat']],
          next_question=e['research_question']))
    return out[:8]

def definition_equality_attempt(files):
    """A small genuine proof-search baseline, never an assumed correspondence."""
    selected=[f['selected_declarations'] for f in files]
    if any(len(ds)!=1 for ds in selected): return None
    a,b=selected[0][0],selected[1][0]
    if any(d.get('kind') not in ('def','definition','abbrev') for d in (a,b)): return None
    type_a=re.sub(r'\s+',' ',str(a.get('type',''))).strip()
    type_b=re.sub(r'\s+',' ',str(b.get('type',''))).strip()
    if type_a!=type_b or not any(s in type_a for s in ('→','∀','ClosureOperator','LinearMap','OrderHom')): return None
    if not all(re.fullmatch(r'[\w.\u00ab\u00bb]+',d['name']) for d in (a,b)): return None
    modules=[f.get('module') for f in files]
    if not all(modules): return None
    return ('\n'.join('import '+m for m in dict.fromkeys(modules))+'\n\n'
      '-- Автоматический кандидат: проверяется только дефинициональное равенство.\n'
      '-- Неуспех rfl означает неуспех этой попытки, а не отсутствие других связей.\n'
      'namespace Bridge\n\n'
      'theorem definition_correspondence : @'+a['name']+' = @'+b['name']+' := by\n  rfl\n\nend Bridge\n')

def assemble_analysis(run_id,inputs,inspection,dataset,targets=None,overrides=None,examples=None):
    outputs=[];targets=targets or ['', ''];overrides=overrides or [[],[]]
    inspected=inspection.get('files',[])
    for i,source in enumerate(inputs):
        info=dict(inspected[i]) if i<len(inspected) else dict(name=source['name'],declarations=[],inspection_status='unavailable')
        decls=info.get('declarations',[])
        target=targets[i].strip() if i<len(targets) and isinstance(targets[i],str) else ''
        if target:
            selected=[d for d in decls if d['name']==target]
            if not selected and inspection.get('semantic_extraction'):
                raise ValueError('Выбранная декларация не найдена в файле '+source['name']+': '+target)
            if not selected: info['target_unresolved']=True
        else: selected=[d for d in decls if d.get('kind') in ('def','definition','structure','inductive','opaque','abbrev')][:12] or decls[:12]
        info.update(name=source['name'],sha256=hashlib.sha256(source['content'].encode()).hexdigest(),target=target,
                    selected_declarations=selected,
                    msc_matches=classify(source['content'],selected,dataset,overrides[i] if i<len(overrides) else None))
        outputs.append(info)
    paths=[]
    if outputs[0]['msc_matches'] and outputs[1]['msc_matches']:
        for a,b in [(outputs[0]['msc_matches'][0]['code'],outputs[1]['msc_matches'][0]['code'])]: paths.append(navigation_path(a,b,dataset))
    candidates,shared=structural_candidates(*outputs)
    candidates+=catalog_candidates(*outputs)
    result=dict(id=run_id,files=outputs,taxonomy_paths=paths,candidates=candidates,
                structural_matches=shared,inspection=inspection,
                notes=['MSC классифицирует темы; полный импорт не означает полноты математического знания.',
                       'Поиск локальный и детерминированный: термины, формальные зависимости, типы и курируемый каталог. Генеративная модель и внешний поиск не подключены.',
                       'Балл MSC — порядок выдачи, не вероятность истинности. Все автоматические тематические метки требуют проверки.',
                       'Ни таксономический путь, ни общая зависимость, ни литературная подсказка не получают статус доказанного соответствия.'])
    attempt=definition_equality_attempt(outputs) if inspection.get('semantic_extraction') else None
    if attempt:
        result.update(bridge_source=attempt,bridge_targets=['Bridge.definition_correspondence'],bridge_origin='generated_definition_equality_attempt')
        result['notes'].append('Предложена автоматическая попытка дефиниционального равенства через rfl. До реального запуска Lean это лишь кандидат; другие виды соответствий требуют отдельной формулировки.')
    for example in examples or []:
        if len(example.get('files',[]))==2 and all(x['name']==y['name'] and x['content']==y['content'] for x,y in zip(inputs,example['files'])):
            result['example_id']=example['id']
            if example.get('bridge_source'):
                result.update(bridge_source=example['bridge_source'],bridge_targets=example.get('bridge_targets',[]),bridge_origin='prepared_control_example')
                result['notes'].append('Это контрольный пример с заранее подготовленным мостом; не слепое математическое открытие.')
            break
    return result
