---
title: system.ml
---

[Original file](https://github.com/jrh13/hol-light/blob/master/system.ml)

This file is also a bit of an awkward one, but it's also mercifully short.

```ocaml
Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };;
```
This is a significant increase in the stack limit.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Make sure user interrupts generate an exception, not kill the process.    *)
(* ------------------------------------------------------------------------- *)

Sys.catch_break true;;
```
This is a significant increase in the stack limit.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Set up a quotation expander for the `...` quotes.                         *)
(* This includes the case `;...` to support miz3, even if that isn't loaded. *)
(* Other quotations ending in `...:` are treated just as (escaped) strings,  *)
(* so they can be parsed in a type context etc.                              *)
(* ------------------------------------------------------------------------- *)

let quotexpander s =
  if s = "" then failwith "Empty quotation" else
  let c = String.sub s 0 1 in
  if c = ":" then
    "parse_type \""^
    (String.escaped (String.sub s 1 (String.length s - 1)))^"\""
  else if c = ";" then "parse_qproof \""^(String.escaped s)^"\"" else
  let n = String.length s - 1 in
  if String.sub s n 1 = ":"
  then "\""^(String.escaped (String.sub s 0 n))^"\""
  else "parse_term \""^(String.escaped s)^"\"";;

Quotation.add "tot" (Quotation.ExStr (fun x -> quotexpander));;
```
Some important code for handling Camlp4 quotations that I just want to skip
over.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Modify the lexical analysis of uppercase identifiers.                     *)
(* ------------------------------------------------------------------------- *)

set_jrh_lexer;;
```
The final piece of magic from Camlp4.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Load in the bignum library and set up printing in the toplevel.           *)
(* ------------------------------------------------------------------------- *)

#load "nums.cma";;

include Num;;

let print_num n =
  Format.open_hbox();
  Format.print_string(string_of_num n);
  Format.close_box();;

#install_printer print_num;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/print_num.html>

Some stuff to handle and display arbitrary precision integers.

- Previous: [hol.ml](hol.md)
- [Index](index.md)
- Next: [lib.ml](lib.md)
