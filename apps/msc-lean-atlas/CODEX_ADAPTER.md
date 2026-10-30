# Codex worker adapter

`research_codex.py` implements the local stdio Codex App Server protocol. It uses
Codex's existing authentication and never reads or exports credentials. Worker
messages are sent to the selected remote model; Lean compilation is a separate
local responsibility of the outer research controller.

## Public interface

```python
import research_codex

connection = research_codex.status(timeout_s=15)
result = research_codex.run_task(
    prompt="A bounded mathematical task with all necessary source evidence",
    work_dir="/absolute/path/to/one-immutable-attempt",
    model="gpt-6-astra",
    timeout_s=120,
    output_schema=None,
    effort="medium",
    on_event=lambda event: None,
    cancelled=lambda: False,
    thread_id=None,
)
```

- `status` returns authenticated presence, model availability, effort options and
  a timestamp. Catalog availability does not itself certify a successful model
  invocation. Account email/IDs and credentials are excluded.
- `run_task` returns `status`, `text`, `thread_id`, `turn_id`, `usage`, `error`,
  `model`, timing, interruption state and attempt ID.
- Only the explicitly selected `gpt-6-astra` is accepted. Provider fallback is
  disabled; a reroute produces `model_mismatch`.
- The timeout bounds the connection and turn together (plus up to three seconds
  for cancellation acknowledgement and process teardown). Usage is measured
  from actual Codex events, not estimated. This is **not a hard token/spend cap**.
- `output_schema` is forwarded to the documented `turn/start.outputSchema`.
- `on_event` receives allowlisted agent messages, usage, turn states and bounded
  error messages. Raw reasoning streams and arbitrary tool outputs are omitted.

## Execution and persistence

The worker uses a read-only sandbox. Shell/exec, agents, apps/plugins, hooks,
browser/computer use and image-generation feature flags are disabled. The worker
is instructed to produce an answer from supplied evidence; the outer controller
owns retrieval, proof execution and scope changes. Server-initiated approval,
client-tool and external-token requests are refused. No approval is granted by
this adapter.

Each attempt directory stores:

- `codex-state.json`: request fingerprint, stable IDs, status, output and usage;
- `codex-events.jsonl`: allowlisted events;
- `codex.lock`: advisory file lock excluding concurrent dispatch for the same
  attempt.

Repeated calls with identical arguments return a terminal result. After an
interrupted client or an uncertain transport outcome, the same directory can be
used to inspect/resume the recorded thread and recover the existing turn. It
never silently issues another generation. An unidentifiable dispatch returns
`needs_review`. A genuinely new attempt requires a different directory.
Changing prompt, model, schema or effort in an existing directory is rejected.

Cancellation/timeout sends `turn/interrupt` where IDs are known and terminates
this adapter's process. Unknown dispatch outcomes remain explicit; closing a
client connection is not a proof that an unknown remote turn was cancelled.

Use `SHAIM_CODEX_BIN` to select the executable, otherwise PATH or the bundled
Codex desktop binary is used. User-wide configuration is not rewritten.

## Verification on 30 October 2026

Local CLI: `codex-cli 0.164.0-alpha.11.1`.

- Actual initialize → account/read → model/list succeeded with existing ChatGPT
  authentication and the exact `gpt-6-astra` catalog entry.
- One tiny real generation completed with structured output
  `{"answer":"SHAIM_ASTRA_OK"}` in 8.994 seconds. Reported usage: 13,851 input
  tokens, 19 output tokens. These tokens include Codex's prompt overhead.
- Recovery of that same completed turn succeeded in 0.61 seconds, with no second
  generation.
- Sixteen unit tests exercise protocol sequencing, refusal of approvals,
  authoritative final text, model mismatch, timeout/cancel, failures,
  idempotency, locking, request identity, schema forwarding and recovery.

Evidence: `verification/codex-adapter-smoke-supported/` and
`verification/codex-adapter-recovery-check/`.

The first pre-inference protocol probe was rejected because this CLI no longer
accepts `readOnly.access`, although the generated schema and online example
still describe it. Its error is preserved in `verification/codex-adapter-smoke/`.
The adapter uses the supported `{"type":"readOnly"}` form.

Run protocol tests without model calls:

```sh
python3 -m unittest discover -s tests -p 'test_research_codex.py' -v
```

Official reference: <https://developers.openai.com/codex/app-server>.
The transport and fields may change with Codex releases; a protocol failure is
reported rather than converted to a mathematical result.
