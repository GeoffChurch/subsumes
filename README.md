# subsumes
Relational term subsumption for SWI-Prolog

`subsumes/2` is intended as a relational drop-in replacement for [`subsumes_term/2`](https://www.swi-prolog.org/pldoc/doc_for?object=subsumes_term/2). It can handle cyclic data, as well as cases where cyclic data would be induced.

```prolog
?- f(X, Y) subsumes G.
G = f(_A, _B),
X subsumes _A,
Y subsumes _B.

?- f(X, Y) subsumes X. % Example with induced cyclic data.
X = f(X, Y).

?- X subsumes Y, X = g(_).
X = g(_A),
Y = g(_B),
_A subsumes _B.
```

See the unit tests in [`prolog/subsumes.plt`](prolog/subsumes.plt) for more examples.

Note that this conflicts with the deprecated [`terms:subsumes/2`](https://www.swi-prolog.org/pldoc/doc_for?object=subsumes/2).

TODO: make ISO-compatible.