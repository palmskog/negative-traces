# Negative Coinductive Traces

Development in Coq of possibly-infinite traces and properties
of such traces via negative coinduction and corecursion, useful
for capturing labeled transition systems.

## Meta

- Author(s):
  - Karl Palmskog
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.16 or later
- Additional dependencies: none
- Coq namespace: `NegativeTraces`

## Building instructions

``` shell
git clone https://github.com/palmskog/negative-traces
cd negative-traces
make   # or make -j <number-of-cores-on-your-machine>
```

## Files

- `Traces.v`: definition and decomposition of possibly-infinite traces

Definitions and properties are inspired by
[Coinductive Trace-Based Semantics for While][coind-sem-url]
by Nakata and Uustalu.

[coind-sem-url]: https://github.com/palmskog/coind-sem-while
