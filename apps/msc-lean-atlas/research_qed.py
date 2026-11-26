"""QED's textual proof workflow adapted to SHAIM's durable Astra App Server turns.

The pinned upstream role instructions and their MIT license live in qed_upstream.
File-based role handoffs are replaced by structured replies and immutable turn keys.
"""
from __future__ import annotations

import json
from pathlib import Path

from research_service import object_schema


UPSTREAM = 'https://github.com/proofQED/QED/tree/bf91aaf8daa763281bdf0dafb46457fc794c11a5'
PROMPTS = Path(__file__).resolve().parent / 'qed_upstream' / 'prompts'
DECOMPOSITION = 'decomposition-prover/'
# Source line ranges in the pinned (unmodified) prompts: the mathematical rubrics,
# without the upstream shell, tool configuration and file output boilerplate.
RUBRICS = {
    'qed_survey': ('literature_survey.md', [(17, 23), (41, 43), (52, 52), (79, 113), (143, 146)]),
    'qed_plan': (DECOMPOSITION + 'decomposition.md', [(9, 18), (30, 73), (192, 231), (241, 289)]),
    'qed_prove': (DECOMPOSITION + 'single_prover.md', [(9, 20), (50, 79), (159, 242), (253, 309), (313, 325)]),
    'qed_structural': (DECOMPOSITION + 'proof_verify_structural.md', [(29, 206), (223, 226)]),
    'qed_detailed': (DECOMPOSITION + 'proof_verify_detailed.md', [(46, 98), (122, 131)]),
    'qed_verdict': (DECOMPOSITION + 'verdict_proof.md', [(9, 10), (18, 24), (38, 45), (63, 67)]),
    'qed_regulator': (DECOMPOSITION + 'regulator.md', [(16, 26), (30, 31), (35, 72)]),
    'qed_summary': ('proof_effort_summary.md', [(15, 41)]),
}
TITLES = {
    'qed_survey': 'Обзор задачи', 'qed_plan': 'План доказательства',
    'qed_prove': 'Доказательство', 'qed_structural': 'Проверка структуры',
    'qed_detailed': 'Проверка деталей', 'qed_verdict': 'Вердикт рецензента',
    'qed_regulator': 'Выбор исправления', 'qed_summary': 'Итоги поиска',
}
TEXT = {'type': 'string'}


def choices(*values):
    return {'type': 'string', 'enum': list(values)}


KIND = choices('proof', 'counterexample', 'inconclusive')
REPORT = object_schema(dict(assessment=choices('PASS', 'FAIL'), body=TEXT))
SCHEMAS = {
    'qed_survey': object_schema(dict(difficulty=choices('Easy', 'Medium', 'Hard'), body=TEXT, answer_kind=KIND, proof=TEXT)),
    'qed_plan': object_schema(dict(body=TEXT)),
    'qed_prove': object_schema(dict(answer_kind=KIND, body=TEXT)),
    'qed_structural': REPORT, 'qed_detailed': REPORT,
    'qed_verdict': object_schema(dict(decision=choices('DONE', 'CONTINUE'))),
    'qed_regulator': object_schema(dict(decision=choices('REVISE_PROOF', 'REVISE_PLAN', 'REWRITE'), body=TEXT)),
    'qed_summary': object_schema(dict(body=TEXT)),
}
INSTRUCTIONS = {
    'qed_survey': 'Return difficulty and body with the justification. For Easy, supply a complete standalone '
                  'solution in proof and set answer_kind. For Medium or Hard, body contains the survey of '
                  'applicable mathematical results and pitfalls; return an empty proof and inconclusive.',
    'qed_plan': 'Write the plan in body. Specify a mode-appropriate approach, ordered STEP identifiers, '
                'dependencies, key steps and the exact GOAL. Use a readable list.',
    'qed_prove': 'Return body with a standalone proof or an explicit counterexample to the claim. If '
                 'there is a gap, label the result inconclusive and describe the strongest justified step.',
    'qed_structural': 'Return assessment + body with the five structural findings, including any changes '
                      'to the claim, unverified dependencies and refuted plan steps. Use FAIL for critical gaps.',
    'qed_detailed': 'Return assessment + body. Check each STEP and the GOAL. Independently check '
                    'the witness and all hypotheses for a counterexample. A critical gap is a FAIL.',
    'qed_verdict': 'Encode the requested single-word verdict in the decision field.',
    'qed_regulator': 'Return decision and body with specific guidance. Identify the failing step and '
                     'what the next agent should retain, repair or replace.',
    'qed_summary': 'Summarize the supplied stage history in body, including the reasoning, reviewer '
                   'findings and remaining gaps. Report the level of evidence as model review.',
}


def _prompt(role, contract, context):
    filename, ranges = RUBRICS[role]
    lines = (PROMPTS / filename).read_text(encoding='utf-8').splitlines()
    rubric = '\n\n'.join('\n'.join(lines[start - 1:end]) for start, end in ranges)
    return f'''Role: {role}. Follow the mathematical criteria from proofQED/QED below.
Transport adaptation: all inputs are included in this message. Any upstream file references mean
the corresponding supplied data. File writes, shell commands, and literature searches are unavailable.
Do not claim to have verified an external citation; prove needed facts from the inputs or flag a gap.
The input question/contract is fixed. A counterexample must satisfy its hypotheses and violate its
claim. If the contract asks for a refutation, label a successful refutation counterexample. Admit
unresolved questions. For a counterexample, apply the same QED review criteria to the refutation.
Write user-facing fields in Russian, with legible formulas and concise Markdown. Return exactly the
requested JSON shape. The following excerpts define the mathematical work; the transport and output
instructions here take precedence over any file, tool, or response format mentioned in the excerpts.

QED rubric:
{rubric}

This turn: {INSTRUCTIONS[role]}

Immutable problem and definitions (JSON):
{json.dumps(contract, ensure_ascii=False)}

Stage inputs (JSON):
{json.dumps(context, ensure_ascii=False)}'''


def _read_output(role, result):
    output = json.loads(result['text'])
    expected = SCHEMAS[role]['properties']
    if not isinstance(output, dict) or set(output) != set(expected):
        raise ValueError(f'QED: неожиданный формат ответа роли {role}.')
    for name, spec in expected.items():
        value = output[name]
        if not isinstance(value, str) or ('enum' in spec and value not in spec['enum']):
            raise ValueError(f'QED: неверное значение {name} в ответе {role}.')
        output[name] = value.strip()
    if 'body' in output and not output['body']:
        raise ValueError(f'QED: роль {role} вернула пустой ответ.')
    return output


def run_workflow(service, run_id):
    """Replay cached turns with deterministic keys and advance until a terminal branch."""
    run = service.get(run_id)
    contract = run['contract']
    full_route = contract.get('qed_route') == 'full'
    state = dict(difficulty=None, review='unreviewed', proof='', answer_kind='inconclusive',
                 steps=[], upstream=UPSTREAM)
    known_steps = {step['key'] for step in (run.get('qed') or {}).get('steps', [])}

    def call(role, key, context, *, title=None):
        result = service._call(run_id, role, _prompt(role, contract, context), key,
                               output_schema=SCHEMAS[role])
        output = _read_output(role, result)
        title = title or TITLES[role]
        body = output.get('body') or output['decision']
        if role == 'qed_survey':
            state['difficulty'] = output['difficulty']
            if output['difficulty'] == 'Easy' and output['proof']:
                state.update(proof=output['proof'], answer_kind=output['answer_kind'])
                if full_route:
                    body += '\n\n## Черновик из обзора\n\n' + output['proof']
        elif role == 'qed_prove':
            state.update(proof=body, answer_kind=output['answer_kind'], review='unreviewed')
        elif role in ('qed_detailed', 'qed_structural') and output['assessment'] == 'FAIL':
            state['review'] = 'changes_requested'
        step = dict(key=key, role=role, title=title, body=body)
        step.update({k: v for k, v in output.items() if k not in ('body', 'proof')})
        state['steps'].append(step)
        # During replay, do not briefly replace a later published stage with an old one.
        if key not in known_steps:
            service.update(run_id, qed=state)
        return output

    def finish(summary):
        outcome = 'unknown' if state['answer_kind'] == 'inconclusive' else 'draft'
        result = dict(status='complete', outcome=outcome, verification='natural_language',
                      summary=summary, upstream=UPSTREAM)
        for field in ('difficulty', 'proof', 'answer_kind', 'review'):
            result[field] = state[field]
        if outcome == 'draft':
            folder = service.folder(run_id) / 'qed'
            folder.mkdir(exist_ok=True)
            temporary = folder / 'proof.tmp'
            temporary.write_text(state['proof'] + '\n', encoding='utf-8')
            temporary.replace(folder / 'proof.txt')
        service.update(run_id, outcome=outcome, result=result, qed=state)

    survey = call('qed_survey', 'qed-survey', {})
    if (not full_route and state['difficulty'] == 'Easy'
            and state['proof'] and state['answer_kind'] != 'inconclusive'):
        finish(survey['body'])
        return

    # Same 8 proof attempts / 4 plan revisions / 4 decompositions as QED's config.
    # SHAIM's persisted call/time budget is an additional bound enforced by _call.
    attempt = revision = proof_number = 1
    plan_mode = 'CREATE'
    plan = ''
    feedback = {}
    history = []
    while attempt <= 4:
        prefix = f'qed-a{attempt}-r{revision}'
        if plan_mode:
            plan_inputs = dict(mode=plan_mode, related_work=survey['body'], history=history,
                               previous_plan=plan, previous_proof=state['proof'], feedback=feedback)
            plan = call('qed_plan', prefix + '-plan', plan_inputs)['body']
        proof_key = f'{prefix}-p{proof_number}'
        proof = call('qed_prove', proof_key + '-prove', dict(plan=plan, related_work=survey['body'],
                     previous_proof=state['proof'], feedback=feedback))
        candidate = dict(plan=plan, candidate=proof)
        structural = call('qed_structural', proof_key + '-structural', candidate)
        reports = {'structural': structural}
        verdict = call('qed_verdict', proof_key + '-structural-verdict', dict(mode='STRUCTURAL', **reports),
                       title='Вердикт по структуре')
        if structural['assessment'] == 'PASS' and verdict['decision'] == 'DONE':
            detailed = call('qed_detailed', proof_key + '-detailed', dict(**candidate, **reports))
            reports['detailed'] = detailed
            verdict = call('qed_verdict', proof_key + '-final-verdict', dict(mode='FINAL', **reports),
                           title='Итоговый вердикт')
            if (detailed['assessment'] == 'PASS' and verdict['decision'] == 'DONE'
                    and proof['answer_kind'] != 'inconclusive'):
                state['review'] = 'model_reviewed'
                break

        state['review'] = 'changes_requested'
        if proof_key + '-regulator' not in known_steps:
            service.update(run_id, qed=state)
        regulator = call('qed_regulator', proof_key + '-regulator',
                         dict(**candidate, reports=reports, verdict=verdict, history=history,
                              attempt=attempt, revision=revision, proof_number=proof_number))
        feedback = dict(reports=reports, guidance=regulator)
        history.append(dict(round=proof_key, action=regulator['decision'], reason=regulator['body'][:1600]))
        decision = regulator['decision']
        if decision == 'REVISE_PROOF' and proof_number < 8:
            proof_number += 1
            plan_mode = None
        elif decision != 'REWRITE' and revision < 4:
            revision += 1
            proof_number = 1
            plan_mode = 'REVISE'
        else:
            attempt += 1
            revision = proof_number = 1
            plan_mode = 'REWRITE'
    else:
        state['answer_kind'] = 'inconclusive'

    service.update(run_id, qed=state)
    current = service.get(run_id)
    if (current['usage']['calls'] < current['budget']['max_calls']
            or any(attempt['id'] == 'qed-summary' for attempt in current['attempts'])):
        # Keep full proof + last review; older attempts are represented by the regulator's
        # diagnosis so the summary does not reinsert every copy of a long proof.
        summary = call('qed_summary', 'qed-summary', dict(proof=state['proof'], reports=reports,
                       history=history, review=state['review'], answer_kind=state['answer_kind']))['body']
    else:
        summary = 'Бюджет вызовов исчерпан после рецензирования. Отдельная сводка не запускалась.'
    finish(summary)
