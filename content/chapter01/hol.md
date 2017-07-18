---
title: hol.ml
---

[Original file](https://github.com/jrh13/hol-light/blob/master/hol.ml)

This file is mostly miscellaneous odds and ends that aren't too important for
the rest of the discussion, but I thought I'd briefly go through them anyway,
for the sake of completeness.

```ocaml
let hol_version = "2.20++";;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/hol_version.html

This variable is used in the generation of the help files.

```ocaml
#directory "+compiler-libs";;
```
This toplevel directive enables the loading of files from the `compiler-libs`
library, described in the OCaml manual
[here](http://caml.inria.fr/pub/docs/manual-ocaml/parsing.html).

```ocaml
let hol_dir = ref
  (try Sys.getenv "HOLLIGHT_DIR" with Not_found -> Sys.getcwd());;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/hol_dir.html

```ocaml
(* ------------------------------------------------------------------------- *)
(* Should eventually change to "ref(Filename.temp_dir_name)".                *)
(* However that's not available in 3.08, which is still the default          *)
(* in Cygwin, and I don't want to force people to upgrade Ocaml.             *)
(* ------------------------------------------------------------------------- *)

let temp_path = ref "/tmp";;
```
Fairly obvious things, I think.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Load in parsing extensions.                                               *)
(* For Ocaml < 3.10, use the built-in camlp4                                 *)
(* and for Ocaml >= 3.10, use camlp5 instead.                                *)
(* ------------------------------------------------------------------------- *)

if let v = String.sub Sys.ocaml_version 0 4 in v >= "3.10"
then (Topdirs.dir_directory "+camlp5";
      Topdirs.dir_load Format.std_formatter "camlp5o.cma")
else (Topdirs.dir_load Format.std_formatter "camlp4o.cma");;

Topdirs.dir_load Format.std_formatter (Filename.concat (!hol_dir) "pa_j.cmo");;
```
This section is a little bit hairy, but I'm going to skip over it for now.
I may at some future time add a section to this guide on the syntax extensions
used by HOL Light.  Or I may not.

Here are some things handled at the Camlp5 level:

http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/it.html

```ocaml
(* ------------------------------------------------------------------------- *)
(* Load files from system and/or user-settable directories.                  *)
(* Paths map initial "$/" to !hol_dir dynamically; use $$ to get the actual  *)
(* $ character at the start of a directory.                                  *)
(* ------------------------------------------------------------------------- *)

let use_file s =
  if Toploop.use_file Format.std_formatter s then ()
  else (Format.print_string("Error in included file "^s);
        Format.print_newline());;

let hol_expand_directory s =
  if s = "$" || s = "$/" then !hol_dir
  else if s = "$$" then "$"
  else if String.length s <= 2 then s
  else if String.sub s 0 2 = "$$" then (String.sub s 1 (String.length s - 1))
  else if String.sub s 0 2 = "$/"
  then Filename.concat (!hol_dir) (String.sub s 2 (String.length s - 2))
  else s;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/hol_expand_directory.html

```ocaml
let load_path = ref ["."; "$"];;

let loaded_files = ref [];;

let file_on_path p s =
  if not (Filename.is_relative s) then s else
  let p' = List.map hol_expand_directory p in
  let d = List.find (fun d -> Sys.file_exists(Filename.concat d s)) p' in
  Filename.concat (if d = "." then Sys.getcwd() else d) s;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/file_on_path.html

```ocaml
let load_on_path p s =
  let s' = file_on_path p s in
  let fileid = (Filename.basename s',Digest.file s') in
  (use_file s'; loaded_files := fileid::(!loaded_files));;

let loads s = load_on_path ["$"] s;;

let loadt s = load_on_path (!load_path) s;;

let needs s =
  let s' = file_on_path (!load_path) s in
  let fileid = (Filename.basename s',Digest.file s') in
  if List.mem fileid (!loaded_files)
  then Format.print_string("File \""^s^"\" already loaded\n") else loadt s;;
```
And these functions are not terribly exciting, but necessary for loading the
HOL system into the toplevel.  In the rest of this guide, I'll skip over this
kind of loading code.

- Previous: [background.ml](background.md)
- [Index](index.md)
- Next: [system.ml](system.md)
