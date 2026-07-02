# subsumes
Relational term subsumption for SWI-Prolog

- `subsumes/2` is intended as a relational drop-in replacement for the anyway deprecated [`terms:subsumes/2`](https://www.swi-prolog.org/pldoc/doc_for?object=subsumes/2). It can handle cyclic data, as well as cases where cyclic data would be induced.

  ```prolog
  ?- f(X, Y) subsumes G.
  G = f(_A, _B),
  X subsumes _A,
  Y subsumes _B.

  ?- f(X) subsumes Y, Y subsumes X. % Example with induced cyclic data.
  X = Y, Y = f(Y).

  ?- X subsumes Y, X = g(_).
  X = g(_A),
  Y = g(_B),
  _A subsumes _B.
  ```

- `subsumes_chk(+General, +Specific)` — holds if `General` can already be guaranteed to permanently subsume `Specific` (corresponding subterms are `==` or `General`'s subsumes `Specific`'s by subsumptive links or by being permavar). If ever true, it will remain true, but if false, it may become true later as subsumptive links are added that guarantee permanent subsumption.
- `is_permavar(+V)` — holds if `V`'s nonvar lower bounds (LBs) antiunify to a var, which guarantees that it can never be unified with a nonvar. You can make your own permavars with e.g. `subsumes(V, apples), subsumes(V, oranges)`.
- `compact_lbs(+V)` — compacts `V`'s LBs, forgetting the originals in some cases, but otherwise a functionally invisible optimization. This is only useful for programs that would be bottlenecked by the sheer size of LB lists.

See the unit tests in [`test/subsumes.plt`](test/subsumes.plt) for more examples.

## Installation in SWI-Prolog

```prolog
?- pack_install(subsumes).
```

## Testing

Run from the project root:
```shell
swipl -p library=prolog -g "expand_file_name('test/*.plt', Files), load_files(Files), run_tests" -t halt
```

---

(Note to self) To publish a new version:
1. update `pack.pl`
2. do GitHub release with new tag matching the pack.pl version
3. execute:
```bash
swipl -g "make_directory(temp), pack_install(subsumes, [url('https://github.com/GeoffChurch/subsumes/archive/0.5.zip'), pack_directory(temp), interactive(false)]), delete_directory_and_contents(temp)" -t halt
```
