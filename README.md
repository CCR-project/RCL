# Refinement Composition Logic

## Dependencies
Our development successfully compiles with the following versions (in Linux):

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
- Rules in Fig. 1 --> `RefFacts` at lib/Algebra.v, and `ModSem_RefFacts` at ems/ModSemFacts.v
- Fig. 2 --> `RPT0`, `RPT1`, `SUCC`, `PUT`, `T_MAIN`, `M_MAIN`, `S_MAIN` at imp/example/Repeat.v
- Sec 1.3, Example involving Fig. 2 --> Theorem `main_rcl` and `main_ref` at imp/example/Repeat.v

Sec. 2 BACKGROUND
- Definition of *Contextual refinement* $⊑_{ctx}$ --> `ref` at ems/ModSem.v

Sec. 3 REFINEMENT COMPOSITION LOGIC
- Definition of *mProp* --> `mProp` at iris/IPM.v
- Fig.3 and Fig.4 --> Provided in iris/IPM.v
- Sec. 3.2, *Example: Rpt module.* --> `Persistent_rpt0` and Lemma `rpt0_spec` at imp/example/Repeat.v
- Sec. 3.3, *Semantics of polysemic programs.* --> `prog: callE ~> itree Es` at ems/ModSem.v

Sec. 4 FOUNDATIONS OF RCL
- Sec. 4.1, Definition of *MRAs* --> Module `MRAS` at lib/Algebra.v
- Fig.6 --> Provided in iris/IPM.v. For examples, 
-- Set of modules --> `Own`
-- The refines modality --> `Refines`
-- The persistence modality --> `Pers`
-- The magic wand --> `Wand`
- Sec. 4.2, Definition of *MRA* --> Module `MRA` at lib/Algebra.v
- The remaining contents in Sec. 4.2, Sec. 4.3 --> Provided in iris/homomorphisms.v

Sec. 5 DERIVED PATTERNS AND THEIR APPLICATIONS
- Sec. 5.1, Definition of *layered refinement*, rules of *layer calculus*, and the example --> Section `CAL` in iris/IPM.v
- Sec. 5.2, Definition of *fancy update* --> `IUpd` at iris/IPM.v
- Sec. 5.2, example --> Provided in imp/example/Stealing.v

Sec. 6 A CONCRETE INSTANCE OF MRA
- Fig.11 --> Collected in FreeSim/Behavior.v
- The *core* operator --> `core_h` at ems/ModSemE.v
- *findDef* --> `prog: callE ~> itree Es` at ems/ModSem.v
- Theorem 6.1 --> Proved by `ModSem_MRA` at ems/ModSemFacts.v

## Additional materials
Integrating conditional refinement into RCL
- *wrapper modality* --> `Wrap` in iris/IPM.v
- Rules for the wrapper modality --> Module `WA` in lib/Algebra.v
- *Conditional refinement.* --> `CondRefines` in iris/IPM.v
- An example involving Rpt --> Section `CCR` in imp/example/Repeat.v
