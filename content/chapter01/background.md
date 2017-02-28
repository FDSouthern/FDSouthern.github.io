---
title: Background
---
# Background

I'm assuming that you've HOL Light installed correctly, so that when you type
```ocaml
#use "hol.ml" ;;
```
at the `ocaml` toplevel, the system loads correctly.  In this chapter, we're
going to walk through the source code of the core HOL Light system that is
loaded by this command.  The most recent commit at the time I began writing
was [this one](https://github.com/jrh13/hol-light/commit/778ad495ceefc3bcbdc7cc94c87e3cb7da4331d9),
but I don't think that the core system has changed much in recent times!

All rights to the source code are obviously held by John Harrison and
contributors.

Let's get started with [hol.ml](hol.md).