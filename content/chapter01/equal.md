---
title: equal.ml
---

[Original file](https://github.com/jrh13/hol-light/blob/master/equal.ml)

Now we're entering the higher-level deductive system.
Basic equality reasoning including conversionals.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Type abbreviation for conversions.                                        *)
(* ------------------------------------------------------------------------- *)

type conv = term->thm;;

(* ------------------------------------------------------------------------- *)
(* A bit more syntax.                                                        *)
(* ------------------------------------------------------------------------- *)

let lhand = rand o rator;;

let lhs = fst o dest_eq;;

let rhs = snd o dest_eq;;

(* ------------------------------------------------------------------------- *)
(* Similar to variant, but even avoids constants, and ignores types.         *)
(* ------------------------------------------------------------------------- *)

let mk_primed_var =
  let rec svariant avoid s =
    if mem s avoid || (can get_const_type s && not(is_hidden s)) then
      svariant avoid (s^"'")
    else s in
  fun avoid v ->
    let s,ty = dest_var v in
    let s' = svariant (mapfilter (fst o dest_var) avoid) s in
    mk_var(s',ty);;

(* ------------------------------------------------------------------------- *)
(* General case of beta-conversion.                                          *)
(* ------------------------------------------------------------------------- *)

let BETA_CONV tm =
  try BETA tm with Failure _ ->
  try let f,arg = dest_comb tm in
      let v = bndvar f in
      INST [arg,v] (BETA (mk_comb(f,v)))
  with Failure _ -> failwith "BETA_CONV: Not a beta-redex";;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/BETA_CONV.html

`` BETA_CONV `(\x. A) y` `` gives `|- (\x. A) y = A[y/x]`

```ocaml
(* ------------------------------------------------------------------------- *)
(* A few very basic derived equality rules.                                  *)
(* ------------------------------------------------------------------------- *)

let AP_TERM tm =
  let rth = REFL tm in
  fun th -> try MK_COMB(rth,th)
            with Failure _ -> failwith "AP_TERM";;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/AP_TERM.html

`` AP_TERM `f` `ASM1 |- a = b` `` gives `ASM1 |- (f a) = (f b)`.

```ocaml
let AP_THM th tm =
  try MK_COMB(th,REFL tm)
  with Failure _ -> failwith "AP_THM";;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/AP_THM.html

`` AP_THM `ASM1 |- f = g` `a` `` gives `ASM1 |- (f a) = (g a)`.

```ocaml
let SYM th =
  let tm = concl th in
  let l,r = dest_eq tm in
  let lth = REFL l in
  EQ_MP (MK_COMB(AP_TERM (rator (rator tm)) th,lth)) lth;;
```
`` SYM `ASM1 |- a = b` `` gives `ASM1 |- b = a`.

```ocaml
let ALPHA tm1 tm2 =
  try TRANS (REFL tm1) (REFL tm2)
  with Failure _ -> failwith "ALPHA";;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ALPHA_UPPERCASE.html

`` ALPHA `(\x.x)` `(\y.y)` `` gives `|- (\x.x) = (\y.y)`.

```ocaml
let ALPHA_CONV v tm =
  let res = alpha v tm in
  ALPHA tm res;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ALPHA_CONV.html

`` ALPHA_CONV `y` `(\x.x)` `` gives `|- (\x.x) = (\y.y)`.

```ocaml
let GEN_ALPHA_CONV v tm =
  if is_abs tm then ALPHA_CONV v tm else
  let b,abs = dest_comb tm in
  AP_TERM b (ALPHA_CONV v abs);;
```
`` GEN_ALPHA_CONV `y` `!x. P[x]` `` gives `|- (!x. P[x]) = (!y. P[y])`
(it looks inside one level of application).

```ocaml
let MK_BINOP op =
  let afn = AP_TERM op in
  fun (lth,rth) -> MK_COMB(afn lth,rth);;
```
`` MK_BINOP `(+)` (`ASM1 |- a = b`, `ASM2 |- c = d`) `` gives
`ASM1+ASM2 |- a + c = b + d`.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Terminal conversion combinators.                                          *)
(* ------------------------------------------------------------------------- *)
```
A conversion takes a term and returns an equality theorem with the term on
the LHS (or it fails).

```ocaml
let (NO_CONV:conv) = fun tm -> failwith "NO_CONV";;
```
`NO_CONV` is a conversion which always fails.

```ocaml
let (ALL_CONV:conv) = REFL;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ALL_CONV.html

`ALL_CONV` is a conversion which always succeeds without changing the term.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Combinators for sequencing, trying, repeating etc. conversions.           *)
(* ------------------------------------------------------------------------- *)

let ((THENC):conv -> conv -> conv) =
  fun conv1 conv2 t ->
    let th1 = conv1 t in
    let th2 = conv2 (rand(concl th1)) in
    TRANS th1 th2;;
```
`c1 THENC c2` rewrites with c1 then c2.

```ocaml
let ((ORELSEC):conv -> conv -> conv) =
  fun conv1 conv2 t ->
    try conv1 t with Failure _ -> conv2 t;;
```
`c1 ORELSEC c2` rewrites with c1; if it fails, it rewrites with c2 instead.

```ocaml
let (FIRST_CONV:conv list -> conv) = end_itlist (fun c1 c2 -> c1 ORELSEC c2);;
```
`FIRST_CONV [c1;...;cn]` rewrites with the first non-failing conversion in the
list.

```ocaml
let (EVERY_CONV:conv list -> conv) =
  fun l -> itlist (fun c1 c2 -> c1 THENC c2) l ALL_CONV;;
```
`EVERY_CONV [c1;...;cn]` rewrites with the first conversion, then the second,
so on until the last.

```ocaml
let REPEATC =
  let rec REPEATC conv t =
    ((conv THENC (REPEATC conv)) ORELSEC ALL_CONV) t in
  (REPEATC:conv->conv);;
```
`REPEATC c` rewrites with c until it fails (and returns the result of the last
successful rewrite).

```ocaml
let (CHANGED_CONV:conv->conv) =
  fun conv tm ->
    let th = conv tm in
    let l,r = dest_eq (concl th) in
    if aconv l r then failwith "CHANGED_CONV" else th;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/CHANGED_CONV.html

`CHANGED_CONV c` rewrites with `c`, but fails if the result is alpha-equivalent
to the original term.

```ocaml
let TRY_CONV conv = conv ORELSEC ALL_CONV;;
```
`TRY_CONV c` rewrites with `c`; if it fails, it does not change the term
(and does not fail).

```ocaml
(* ------------------------------------------------------------------------- *)
(* Subterm conversions.                                                      *)
(* ------------------------------------------------------------------------- *)

let (RATOR_CONV:conv->conv) =
  fun conv tm ->
    match tm with
      Comb(l,r) -> AP_THM (conv l) r
    | _ -> failwith "RATOR_CONV: Not a combination";;
```
`RATOR_CONV c` uses the conversion to rewrite the operator of a combination.

```ocaml
let (RAND_CONV:conv->conv) =
  fun conv tm ->
   match tm with
     Comb(l,r) -> MK_COMB(REFL l,conv r)
   |  _ -> failwith "RAND_CONV: Not a combination";;
```
`RAND_CONV c` uses the conversion to rewrite the operand of a combination.

```ocaml
let LAND_CONV = RATOR_CONV o RAND_CONV;;
```
`LAND_CONV c` uses the conversion to rewrite the first argument of a binary
function.

```ocaml
let (COMB2_CONV: conv->conv->conv) =
  fun lconv rconv tm ->
   match tm with
     Comb(l,r) -> MK_COMB(lconv l,rconv r)
  | _ -> failwith "COMB2_CONV: Not a combination";;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/COMB2_CONV.html

`COMB2_CONV c1 c2` uses `c1` to rewrite the operator and `c2` to rewrite the
operand of a combination.

```ocaml
let COMB_CONV = W COMB2_CONV;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/COMB_CONV.html

`COMB_CONV c` rewrites both the operator and operand of a combination with `c`.

```ocaml
let (ABS_CONV:conv->conv) =
  fun conv tm ->
    let v,bod = dest_abs tm in
    let th = conv bod in
    try ABS v th with Failure _ ->
    let gv = genvar(type_of v) in
    let gbod = vsubst[gv,v] bod in
    let gth = ABS gv (conv gbod) in
    let gtm = concl gth in
    let l,r = dest_eq gtm in
    let v' = variant (frees gtm) v in
    let l' = alpha v' l and r' = alpha v' r in
    EQ_MP (ALPHA gtm (mk_eq(l',r'))) gth;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ABS_CONV.html

`ABS_CONV c` rewrites the body of an abstraction with `c`.

```ocaml
let BINDER_CONV conv tm =
  if is_abs tm then ABS_CONV conv tm
  else RAND_CONV(ABS_CONV conv) tm;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/BINDER_CONV.html

`BINDER_CONV c` rewrites the body of an abstraction or of a binder/abstraction
combination.

```ocaml
let SUB_CONV conv tm =
  match tm with
    Comb(_,_) -> COMB_CONV conv tm
  | Abs(_,_) -> ABS_CONV conv tm
  | _ -> REFL tm;;
```
`SUB_CONV c` either rewrites both parts of a combination, or the body of an
abstraction, or does nothing (it never fails).

```ocaml
let BINOP_CONV conv tm =
  let lop,r = dest_comb tm in
  let op,l = dest_comb lop in
  MK_COMB(AP_TERM op (conv l),conv r);;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/BINOP_CONV.html

`BINOP_CONV c` rewrites both arguments of a binary function.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Depth conversions; internal use of a failure-propagating `Boultonized'    *)
(* version to avoid a great deal of reuilding of terms.                      *)
(* ------------------------------------------------------------------------- *)

let (ONCE_DEPTH_CONV: conv->conv),
    (DEPTH_CONV: conv->conv),
    (REDEPTH_CONV: conv->conv),
    (TOP_DEPTH_CONV: conv->conv),
    (TOP_SWEEP_CONV: conv->conv) =
  let THENQC conv1 conv2 tm =
    try let th1 = conv1 tm in
        try let th2 = conv2(rand(concl th1)) in TRANS th1 th2
        with Failure _ -> th1
    with Failure _ -> conv2 tm
```
`THENQC c1 c2` is like `(c1 THENC c2) ORELSEC c1 ORELSEC c2`.

```ocaml
  and THENCQC conv1 conv2 tm =
    let th1 = conv1 tm in
    try let th2 = conv2(rand(concl th1)) in TRANS th1 th2
    with Failure _ -> th1
```
`THENCQC c1 c2` is like `(c1 THENC c2) ORELSEC c1`.

```ocaml
  and COMB_QCONV conv tm =
    match tm with
      Comb(l,r) ->
        (try let th1 = conv l in
             try let th2 = conv r in MK_COMB(th1,th2)
             with Failure _ -> AP_THM th1 r
         with Failure _ -> AP_TERM l (conv r))
    | _ -> failwith "COMB_QCONV: Not a combination" in
```
`COMB2_QCONV c1 c2` is like
`(RATOR_CONV c1 THENC RAND_CONV c2) ORELSEC RATOR_CONV c1 ORELSEC RAND_CONV c2`.
`COMB_QCONV c` is like `COMB2_QCONV c c`.

```ocaml
  let rec REPEATQC conv tm = THENCQC conv (REPEATQC conv) tm in
```
`REPEATQC c` rewrites with c one or more times, until it fails (returning the
last succeeding rewrite; if the initial rewrite fails, then `REPEATQC` fails).

```ocaml
  let SUB_QCONV conv tm =
    match tm with
      Abs(_,_) -> ABS_CONV conv tm
    | _ -> COMB_QCONV conv tm in
```
`SUB_QCONV c` is like `ABS_CONV c ORELSEC COMB_QCONV c`.

```ocaml
  let rec ONCE_DEPTH_QCONV conv tm =
      (conv ORELSEC (SUB_QCONV (ONCE_DEPTH_QCONV conv))) tm
```
`ONCE_DEPTH_QCONV c` uses `c` to rewrite all maximal applicable terms (terms
which are not properly contained in another applicable term).  Fails if `c` does
not apply to any terms.

```ocaml
  and DEPTH_QCONV conv tm =
    THENQC (SUB_QCONV (DEPTH_QCONV conv))
           (REPEATQC conv) tm
```
`DEPTH_QCONV c` repeatedly rewrites with `c` (in a single bottom-up sweep),
failing if `c` does not apply anywhere.

```ocaml
  and REDEPTH_QCONV conv tm =
    THENQC (SUB_QCONV (REDEPTH_QCONV conv))
           (THENCQC conv (REDEPTH_QCONV conv)) tm
```
`REDEPTH_QCONV c` rewrites with `c` (in a bottom-up sweep); after any successful
rewrite, it starts over again at the leaves of the new term.  Fails if `c` does
not apply anywhere.

```ocaml
  and TOP_DEPTH_QCONV conv tm =
    THENQC (REPEATQC conv)
           (THENCQC (SUB_QCONV (TOP_DEPTH_QCONV conv))
                    (THENCQC conv (TOP_DEPTH_QCONV conv))) tm
```
`TOP_DEPTH_QCONV c` repeatedly rewrites with `c` top-to-bottom; recursively do
something like:
```
do (rewrite current until no change)
  then rewrite children with TOP_DEPTH_QCONV
until no change
```

```ocaml
  and TOP_SWEEP_QCONV conv tm =
    THENQC (REPEATQC conv)
           (SUB_QCONV (TOP_SWEEP_QCONV conv)) tm in
```
`TOP_SWEEP_QCONV c` rewrite with `c` top-to-bottom; something like:
                (rewrite current until no change)
                then rewrite children with `TOP_SWEEP_QCONV`

```ocaml
  (fun c -> TRY_CONV (ONCE_DEPTH_QCONV c)),
  (fun c -> TRY_CONV (DEPTH_QCONV c)),
  (fun c -> TRY_CONV (REDEPTH_QCONV c)),
  (fun c -> TRY_CONV (TOP_DEPTH_QCONV c)),
  (fun c -> TRY_CONV (TOP_SWEEP_QCONV c));;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/DEPTH_CONV.html

`ONCE_DEPTH_CONV`, `DEPTH_CONV`, `REDEPTH_CONV`, `TOP_DEPTH_CONV`,
`TOP_SWEEP_CONV`:  like the `QCONV` variants, except they never fail.


This has been moved/removed, but exists in other files like
`Examples/hol88.ml` and `Library/analysis.ml`:

`SINGLE_DEPTH_CONV c` rewrites maximal applicable subterms with `c`, then
rewrites parents of changed terms bottom-up.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Apply at leaves of op-tree; NB any failures at leaves cause failure.      *)
(* ------------------------------------------------------------------------- *)

let rec DEPTH_BINOP_CONV op conv tm =
  match tm with
    Comb(Comb(op',l),r) when Pervasives.compare op' op = 0 ->
      let l,r = dest_binop op tm in
      let lth = DEPTH_BINOP_CONV op conv l
      and rth = DEPTH_BINOP_CONV op conv r in
      MK_COMB(AP_TERM op' lth,rth)
  | _ -> conv tm;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/DEPTH_BINOP_CONV.html

`DEPTH_BINOP_CONV op c`
For example, ``DEPTH_BINOP_CONV `+` c`` rewrites `x`,`y`,`z`,`w` in
`` `(x + ((y + z) + w))` `` (fails if any of these rewrites fail).

```ocaml
(* ------------------------------------------------------------------------- *)
(* Follow a path.                                                            *)
(* ------------------------------------------------------------------------- *)

let PATH_CONV =
  let rec path_conv s cnv =
    match s with
      [] -> cnv
    | "l"::t -> RATOR_CONV (path_conv t cnv)
    | "r"::t -> RAND_CONV (path_conv t cnv)
    | _::t -> ABS_CONV (path_conv t cnv) in
  fun s cnv -> path_conv (explode s) cnv;;
```
`PATH_CONV path c`
For example, `PATH_CONV ["b";"l";"r";"r"] c` rewrites the operand of the operand
of the operator of the abstraction body with `c`.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Follow a pattern                                                          *)
(* ------------------------------------------------------------------------- *)

let PAT_CONV =
  let rec PCONV xs pat conv =
    if mem pat xs then conv
    else if not(exists (fun x -> free_in x pat) xs) then ALL_CONV
    else if is_comb pat then
      COMB2_CONV (PCONV xs (rator pat) conv) (PCONV xs (rand pat) conv)
    else
      ABS_CONV (PCONV xs (body pat) conv) in
  fun pat -> let xs,pbod = strip_abs pat in PCONV xs pbod;;

(* ------------------------------------------------------------------------- *)
(* Symmetry conversion.                                                      *)
(* ------------------------------------------------------------------------- *)

let SYM_CONV tm =
  try let th1 = SYM(ASSUME tm) in
      let tm' = concl th1 in
      let th2 = SYM(ASSUME tm') in
      DEDUCT_ANTISYM_RULE th2 th1
  with Failure _ -> failwith "SYM_CONV";;
```
`SYM_CONV` rewrites `` `a = b` `` to `` `b = a` ``.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Conversion to a rule.                                                     *)
(* ------------------------------------------------------------------------- *)

let CONV_RULE (conv:conv) th =
  EQ_MP (conv(concl th)) th;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/CONV_RULE.html

`CONV_RULE c th` uses `c` to rewrite the conclusion of the theorem (and return a
new theorem).

```ocaml
(* ------------------------------------------------------------------------- *)
(* Substitution conversion.                                                  *)
(* ------------------------------------------------------------------------- *)

let SUBS_CONV ths tm =
  try if ths = [] then REFL tm else
      let lefts = map (lhand o concl) ths in
      let gvs = map (genvar o type_of) lefts in
      let pat = subst (zip gvs lefts) tm in
      let abs = list_mk_abs(gvs,pat) in
      let th = rev_itlist
        (fun y x -> CONV_RULE (RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV)
                              (MK_COMB(x,y))) ths (REFL abs) in
      if rand(concl th) = tm then REFL tm else th
  with Failure _ -> failwith "SUBS_CONV";;
```
`SUBS_CONV ths` is a conversion.  It takes its list of equality theorems and
rewrites (anywhere in its argument term) any lhs to its corresponding rhs
(matching with alpha-equivalence).

```ocaml
(* ------------------------------------------------------------------------- *)
(* Get a few rules.                                                          *)
(* ------------------------------------------------------------------------- *)

let BETA_RULE = CONV_RULE(REDEPTH_CONV BETA_CONV);;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/BETA_RULE.html

`BETA_RULE thm` applies all possible beta reductions to `thm` and returns the
new theorem.

```ocaml
let GSYM = CONV_RULE(ONCE_DEPTH_CONV SYM_CONV);;
```
`GSYM thm` applies symmetry on all outermost equalities in the conclusion of
`thm`.

```ocaml
let SUBS ths = CONV_RULE (SUBS_CONV ths);;
```
`SUBS thm` applies `SUBS_CONV` to the conclusion `thm`.

```ocaml
(* ------------------------------------------------------------------------- *)
(* A cacher for conversions.                                                 *)
(* ------------------------------------------------------------------------- *)

let CACHE_CONV =
  let ALPHA_HACK th =
    let tm' = lhand(concl th) in
    fun tm -> if tm' = tm then th else TRANS (ALPHA tm tm') th in
  fun conv ->
    let net = ref empty_net in
    fun tm -> try tryfind (fun f -> f tm) (lookup tm (!net))
              with Failure _ ->
                  let th = conv tm in
                  (net := enter [] (tm,ALPHA_HACK th) (!net); th);;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/CACHE_CONV.html

`CACHE_CONV c` is equivalent to `c`, except that it caches all conversion
applications.

- Previous: [parser.ml](parser.md)
- [Index](index.md)
- Next: [bool.ml](bool.md)
