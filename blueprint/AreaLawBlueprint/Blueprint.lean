import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import AreaLawBlueprint.TexPrelude
import AreaLawBlueprint.Chapters.S01_Introduction
import AreaLawBlueprint.Chapters.S02_Preliminaries
import AreaLawBlueprint.Chapters.S03_InitialBox
import AreaLawBlueprint.Chapters.S04_Quasilocal
import AreaLawBlueprint.Chapters.S05_Conditional
import AreaLawBlueprint.Chapters.S06_Replicas
import AreaLawBlueprint.Chapters.S07_Transport
import AreaLawBlueprint.Chapters.S08_Comparators
import AreaLawBlueprint.Chapters.S09_Scanner
import AreaLawBlueprint.Chapters.S10_Amplification
import AreaLawBlueprint.Chapters.S11_Geometry

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "A two-dimensional area law from a global spectral gap: blueprint" =>

The blueprint of the Lean formalization of the paper (`paper/paper.pdf`). One chapter per paper section, one node per digest anchor with a Lean declaration, labelled by its anchor id (`D<section>.<n>`, `digest/`); statements and proof steps are the digest's, the dependency edges its *Used from* lists, and each node names its Lean declaration. Where the formal proof takes another route than the paper, the proof says so (`RefactoringResult.md` §5).

Paper numbering to anchors:

§1: Thm 1.1 = {bpref "D1.4"}[D1.4] (statement) / {bpref "D11.26"}[D11.26] (proof); Cor 1.2 = {bpref "D1.7"}[D1.7]; Lemma 11.1 also quoted as D1.12.

§2: Lemma 2.1 = {bpref "D2.4"}[D2.4]; Lemma 2.2 = {bpref "D2.12"}[D2.12].

§3: Lemma 3.1 = {bpref "D3.1"}[D3.1]; Lemma 3.2 = {bpref "D3.4"}[D3.4]; Prop 3.3 = {bpref "D3.16"}[D3.16].

§4: Lemma 4.1 = {bpref "D4.4"}[D4.4]; Lemma 4.2 = {bpref "D4.5"}[D4.5]; Prop 4.3 = {bpref "D4.6"}[D4.6]; Lemma 4.4 = {bpref "D4.10"}[D4.10]; Prop 4.5 = {bpref "D4.11"}[D4.11].

§5: Lemma 5.1 = {bpref "D5.5"}[D5.5]; Lemma 5.2 = {bpref "D5.12"}[D5.12]; Lemma 5.3 = {bpref "D5.15"}[D5.15].

§6: Lemma 6.1 = {bpref "D6.4"}[D6.4]; Lemma 6.2 = {bpref "D6.6"}[D6.6]; Lemma 6.3 = {bpref "D6.10"}[D6.10]; Lemma 6.4 = {bpref "D6.12"}[D6.12].

§7: Lemma 7.1 = {bpref "D7.3"}[D7.3]; Lemma 7.2 = {bpref "D7.5"}[D7.5]; Lemma 7.3 = {bpref "D7.7"}[D7.7]; Prop 7.4 = {bpref "D7.14"}[D7.14].

§8: Prop 8.1 = {bpref "D8.8"}[D8.8].

§9: Lemma 9.1 = {bpref "D9.8"}[D9.8]; Prop 9.2 = {bpref "D9.9"}[D9.9]; Def 9.3 = {bpref "D9.14"}[D9.14]; Lemma 9.4 = {bpref "D9.15"}[D9.15]; Prop 9.5 = {bpref "D9.19"}[D9.19]; Prop 9.6 = {bpref "D9.25"}[D9.25].

§10: Lemma 10.1 = {bpref "D10.2"}[D10.2]; Prop 10.2 = {bpref "D10.4"}[D10.4].

§11: Lemma 11.1 = {bpref "D11.1"}[D11.1]; Prop 11.2 = {bpref "D11.4"}[D11.4]; Lemma 11.3 = {bpref "D11.13"}[D11.13]; Lemma 11.4 = {bpref "D11.15"}[D11.15]; Lemma 11.5 = {bpref "D11.18"}[D11.18].

{include 0 AreaLawBlueprint.Chapters.S01_Introduction}

{include 0 AreaLawBlueprint.Chapters.S02_Preliminaries}

{include 0 AreaLawBlueprint.Chapters.S03_InitialBox}

{include 0 AreaLawBlueprint.Chapters.S04_Quasilocal}

{include 0 AreaLawBlueprint.Chapters.S05_Conditional}

{include 0 AreaLawBlueprint.Chapters.S06_Replicas}

{include 0 AreaLawBlueprint.Chapters.S07_Transport}

{include 0 AreaLawBlueprint.Chapters.S08_Comparators}

{include 0 AreaLawBlueprint.Chapters.S09_Scanner}

{include 0 AreaLawBlueprint.Chapters.S10_Amplification}

{include 0 AreaLawBlueprint.Chapters.S11_Geometry}

{blueprint_graph}

{blueprint_summary}
