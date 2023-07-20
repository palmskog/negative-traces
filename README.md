# Negative Traces

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/palmskog/negative-traces/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/palmskog/negative-traces/actions?query=workflow:"Docker%20CI"

Development in Coq of possibly-infinite traces and properties
of such traces via negative coinduction and corecursion, useful
for describing labeled transition systems.

## Meta

- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - [coinduction](https://github.com/damien-pous/coinduction) 1.7 or later
- Coq namespace: `NegativeTraces`

## Building instructions

``` shell
git clone https://github.com/palmskog/negative-traces
cd negative-traces
make   # or make -j <number-of-cores-on-your-machine>
```

## Files

- `Traces.v`: definition, operations, and properties of possibly-infinite traces

## Documentation

Definitions and properties are inspired by
[Coinductive Trace-Based Semantics for While][coind-sem-url]
and [Choice Trees][choice-trees-url].

[coind-sem-url]: https://github.com/palmskog/coind-sem-while
[choice-trees-url]: https://github.com/vellvm/ctrees
