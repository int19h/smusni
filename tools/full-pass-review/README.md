# Full-pass review bundle

This helper concatenates the documents used by a Smusni full-pass review and
records each input's line count and SHA-256. It is independent of Herdr Collab:
it reads no session or participant registry and never reads or writes mail.

Supply an explicit positive generation label:

```sh
python3 tools/full-pass-review/bundle.py --generation 3
```

The output is the ignored file `review/bundle/full-pass-3.md`. Use `--docs` to
replace the default document list. The label is a project convention for
distinguishing full-pass cohorts and artifacts, not a protocol counter or an
enforced workflow state. The last historical review-exchange generation was 2,
so 3 is the natural next label if continuity is useful; a task may choose a
different positive label explicitly.

For a coordinated pass, use fresh task-specific session handles such as
`fable-g3` and `kimi-g3`. A coordinator may create an optional recipient group
such as `@full-pass-g3`; neither the handles nor the group confer a role,
review allocation, consensus rule, or acceptance authority. Record those
choices in the GitHub issue or task brief, use the explicit Herdr Collab
project id `smusni`, and publish review results or handoffs as durable mail.
