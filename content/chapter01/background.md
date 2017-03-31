---
title: Background
---
# Background

This document is very much a **work in progress**.

I'm assuming that you've HOL Light installed correctly, so that when you type
```ocaml
#use "hol.ml" ;;
```
at the `ocaml` toplevel, the system loads correctly.  In this chapter, we're
going to walk through the source code of the core HOL Light system that is
loaded by this command.  The most recent commit at the time I began writing
was [this one](https://github.com/jrh13/hol-light/commit/778ad495ceefc3bcbdc7cc94c87e3cb7da4331d9),
but I'll try and keep up with changes to the system.

All rights to the source code are obviously held by John Harrison and
contributors.

This guide contains text taken from an older summary written by Carl Witty.

- [Index](index.md)
- Next: [hol.ml](hol.md)
