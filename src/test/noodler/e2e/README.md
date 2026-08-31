# Noodler end-to-end tests

Put SMT-LIB v2 testcases in this directory (sub-folders are allowed). Each
smt2 file must:

- contain `(set-info :status <sat|unsat|unknown>)` directive (can also be commented out);
- include at least one `(check-sat)` command (it is ignored during parsing and
  re-issued by the harness).

During testing, the harness rebuilds the command context, ignores user
`check-sat` commands and invokes its own call to ensure the reported status
matches `:status`. Note that only the first `:status` directive is used, which
is useful if the status is known, but it is expected for Z3-Noodler to return
`unknown`. In that case you can put commented out `; (set-info :status unknown)`
before the correct `:status`.
When the solver produces a model for a satisfiable script, the harness extracts
that model from the solver output, asserts the bindings back into the script,
and checks satisfiability again.
