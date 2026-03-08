import Lean
import Lean.Elab.Term
import VersoManual
import TextbookTemplate.Meta.Lean
import TextbookTemplate.Papers

import TextbookTemplate.Preliminaries
import TextbookTemplate.Stlc

open Lean Elab Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open TextbookTemplate

set_option pp.rawOnError true
set_option quotPrecheck false

#doc (Manual) "Software Foundations in Lean" =>

%%%
authors := ["Steven Holtzen"]
%%%

{include TextbookTemplate.Preliminaries}
{include TextbookTemplate.Stlc}
