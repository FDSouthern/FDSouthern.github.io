From <http://www.cl.cam.ac.uk/~jrh13/papers/hollight.html>

```ocaml
(* ------------------------------------------------------------------------- *)
(* Basic equality properties; TRANS is derivable but included for efficiency *)
(* ------------------------------------------------------------------------- *)

  let REFL tm =
    Sequent([],safe_mk_eq tm tm)
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/REFL.html>

`` REFL `x` `` gives `|- x = x`.

```ocaml
  let TRANS (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    match (c1,c2) with
      Comb((Comb(Const("=",_),_) as eql),m1),Comb(Comb(Const("=",_),m2),r)
        when alphaorder m1 m2 = 0 -> Sequent(term_union asl1 asl2,Comb(eql,r))
    | _ -> failwith "TRANS"
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/TRANS.html>

`` TRANS `ASM1 |- a = b` `ASM2 |- b = c` `` gives `ASM1+ASM2 |- a = c`.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Congruence properties of equality.                                        *)
(* ------------------------------------------------------------------------- *)

  let MK_COMB(Sequent(asl1,c1),Sequent(asl2,c2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2) ->
        (match type_of r1 with
           Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of r2) = 0
             -> Sequent(term_union asl1 asl2,
                        safe_mk_eq (Comb(l1,l2)) (Comb(r1,r2)))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/MK_COMB_UPPERCASE.html>

`` MK_COMB (`ASM1 |- f = g`, `ASM2 |- a = b`) `` gives
`ASM1+ASM2 |- (f a) = (g b)`.

```ocaml
  let ABS v (Sequent(asl,c)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const("=",_),l),r) when not(exists (vfree_in v) asl)
         -> Sequent(asl,safe_mk_eq (Abs(v,l)) (Abs(v,r)))
    | _ -> failwith "ABS";;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ABS.html>

`` ABS `x` `ASM1{-x} |- a=b` `` gives `ASM1 |- \x.a = \x.b`.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Trivial case of lambda calculus beta-conversion.                          *)
(* ------------------------------------------------------------------------- *)

  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when Pervasives.compare arg v = 0
        -> Sequent([],safe_mk_eq tm bod)
    | _ -> failwith "BETA: not a trivial beta-redex"
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/BETA.html>

`` BETA `(\x.x) x` `` gives `|- (\x. x) x = x`.

In practice, you probably want to use `BETA_CONV` as defined in
[equal.ml](equal.md).

```ocaml
(* ------------------------------------------------------------------------- *)
(* Rules connected with deduction.                                           *)
(* ------------------------------------------------------------------------- *)

  let ASSUME tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then Sequent([tm],tm)
    else failwith "ASSUME: not a proposition"
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ASSUME.html>

`` ASSUME `a` `` gives `a |- a`.

```ocaml
  let EQ_MP (Sequent(asl1,eq)) (Sequent(asl2,c)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when alphaorder l c = 0
        -> Sequent(term_union asl1 asl2,r)
    | _ -> failwith "EQ_MP"
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/EQ_MP.html>

`` EQ_MP `ASM1 |- a = b` `ASM2 |- a` `` gives `ASM1+ASM2 |- b`.

```ocaml
  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2',safe_mk_eq c1 c2)
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/DEDUCT_ANTISYM_RULE.html>

`` DEDUCT_ANTISYM_RULE `ASM1 |- a` `ASM2 |- b` `` gives
`(ASM1-{b})+(ASM2-{a}) |- a=b`.

To me, this is by far the weirdest rule.  It makes sense in the single sentence
case (if from `p` you can derive `q` and from `q` you can derive `p`, then
`p` and `q` have the same truth value), but in the general case, I'm less sure.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Type and term instantiation.                                              *)
(* ------------------------------------------------------------------------- *)

  let INST_TYPE theta (Sequent(asl,c)) =
    let inst_fn = inst theta in
    Sequent(term_image inst_fn asl,inst_fn c)
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/INST_TYPE.html>

`INST_TYPE instantiation theorem` gives a new theorem with type variables
instantiated.

```ocaml
  let INST theta (Sequent(asl,c)) =
    let inst_fun = vsubst theta in
    Sequent(term_image inst_fun asl,inst_fun c)
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/INST_UPPERCASE.html>

`INST instantiation theorem` gives a new theorem with variables instantiated.

```ocaml
let ETA_AX = new_axiom
  `!t:A->B. (\x. t x) = t`;;

let SELECT_AX = new_axiom
 `!P (x:A). P x ==> P((@) P)`;;

let INFINITY_AX = new_axiom
  `?f:ind->ind. ONE_ONE f /\ ~(ONTO f)`;;
```

`INFINITY_AX` is only used once.
