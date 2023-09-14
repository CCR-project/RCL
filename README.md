# Refinement Composition Logic

## Dependencies
Our development successfully compiles with following versions (in Linux):

- coq (= *8.15.2*)

- coq-ext-lib (= *0.11.8*)
- coq-iris (= *4.0.0*)
- coq-itree (= *4.0.0*)
- coq-ordinal (= *0.5.2*)
- coq-paco (= *4.1.2*)
- coq-stdpp (= *1.8.0*)

All packages can be installed from [OPAM archive for Coq](https://github.com/coq/opam-coq-archive)

## How to build
- make -j[N] -k

## Mapping from the paper to the code
Sec. 1 INTRODUCTION
- Definition of \emph{Contextual refinement} $⊑_{ctx}$ --> `ref` at ems/ModSem.v
- Fig. 1 --> `RefFacts` at lib/Algebra.v, and `ModSem_RefFacts` at ems/ModSemFacts.v
- Fig. 2 --> `RPT0`, `RPT1`, `SUCC`, `PUT` at imp/example/Repeat.v
- Sec 1.2, Example involving Fig. 2 --> Theorem `rpts_ref` at imp/example/Repeat.v

Sec. 3 REFINEMENT COMPOSITION LOGIC
- Definition of \emph{mProp} --> `mProp` at iris/IPM.v
- Fig.4 and Fig.5 --> Provided in iris/IPM.v
- Sec. 3.2, \emph{Example: Rpt module.} --> Lemma `rpt0_spec` at imp/example/Repeat.v
- Sec. 3.3, \emph{Semantics of polysemic programs.} --> `prog: callE ~> itree Es` at ems/ModSem.v

Sec. 4 FOUNDATIONS OF RCL
- Sec. 4.1, Definition of `MRAs` --> Module `MRAS` at lib/Algebra.v
- Fig.7 --> Provided in iris/IPM.v. For examples, 
-- Set of modules --> `Own`
-- The refines modality --> `Refines`
-- The persistence modality --> `Pers`
-- The magic wand --> `wand`
- Contents in Sec. 4.2, Sec. 4.3 --> Provided in iris/homomorphisms.v
-- For example, `MRA` --> Section `MRA`

Sec. 5 DERIVED PATTERNS AND THEIR APPLICATIONS
- Sec. 5.1, Definition of `layered refinement`, rules of `layer calculus` (also Fig.3), and the example --> Section `CAL` in iris/IPM.v
- Sec. 5.2, Definition of \emph{fancy update} --> `IUpd` at iris/IPM.v
- Sec. 5.2, example --> Provided in imp/example/Stealing.v

Sec. 6 A CONCRETE INSTANCE OF MRA
- Fig.6 --> Collected in FreeSim/Behavior.v
- The \emph{core} operator --> `core_h` at ems/ModSemE.v
- findDef --> `prog: callE ~> itree Es` at ems/ModSem.v
- Theorem 6.1 --> Proved by `ModSem_MRA` at ems/ModSemFacts.v

Sec. 7 INTEGRATING CONDITIONAL REFINEMENT INTO RCL
- Sec. 7.2 \emph{wrapper modality} --> `Wrap` in iris/IPM.v
- Rules for the wrapper modality --> Module `WA` in lib/Algebra.v
- \emph{Conditional refinement.} --> `CondRefines` in iris/IPM.v
- Example involving Rpt --> Section `CCR` in imp/example/Repeat.v
