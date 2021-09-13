# Verified Type-Reconstruction/Inference

Herein lies a (partially) verified framework for type-reconstruction.

## Building & Running

To build, enter
```bash
make
```

To run, enter
```bash
dune exec ./bin/main.exe <TODO semantics> -- <TODO options>
```

To clean build files, enter
```bash
make clean
```

### MacOS Quirks

Upon building, you may encounter the following output:
```bash
    ocamlopt bin/main.exe
ld: warning: directory not found for option '-L/opt/local/lib'
```
This message indicates nothing & may be ignored.
However, to silence this churlish notification
one may create the directory
```bash
/opt/local/lib
```
via
```
cd /
sudo mkdir opt/local
sudo mkdir opt/lib
```

## Syntax

Let `x` range over variable names,
`n` range over naturals, `b` range over bools,
& `e` range over terms.

```
e ::= x | n | b | fun x . e | e1 e2 |
  | e1 && e2 | e1 `||` e2 | e1 + e2 | e1 - e2 | e1 = e2 | e1 < e2
  | let x := e1 in e2 | if e1 then e2 else e3
```