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
Sec. 2 BACKGROUND
- Definition of *Contextual refinement* $⊑_{ctx}$ --> `ref` at ems/ModSem.v
- Rules in Fig. 2 --> `RefFacts` at lib/Algebra.v, and `ModSem_RefFacts` at ems/ModSemFacts.v
- Fig. 4 --> `RPT0`, `RPT1`, `SUCC`, `PUT`, `T_MAIN`, `M_MAIN`, `S_MAIN` at imp/example/Repeat.v

Sec. 3 TUTORIAL
- Sec 3.1, Fig. 3 --> iris/IPMDemo.v
- Sec 3.2, Example involving Fig. 4 --> Theorem `main_rcl`, `main_ref`, `Persistent_rpt0`, `rpt0_spec` at imp/example/Repeat.v

Sec. 5 REFINEMENT COMPOSITION LOGIC
- Sec. 5.1, Fig. 6 (Definition of *MRAs*) --> Module `MRAS` at lib/Algebra.v
- Definition of *mProp* --> `mProp` at iris/IPM.v
- Fig. 5 and Fig. 7 --> Provided in iris/IPM.v. For examples,
-- Set of modules --> `Own`
-- The refines modality --> `Refines`
-- The persistence modality --> `Pers`
-- The magic wand --> `Wand`
- Fig. 8 --> `mProp_bi_mixin` and `mProp_bupd_mixin` in iris/IPM.v

Sec. 6 MORE ON ALGEBRAS
- Def.2 (Definition of *MRA*) --> Module `MRA` at lib/Algebra.v
- Sec. 6.2 --> Provided in iris/homomorphisms.v

Sec. 7 DERIVED PATTERNS AND THEIR APPLICATIONS
- Sec. 7.1, Definition of *layered refinement*, rules of *layer calculus*, and the example --> `SECTION CAL` in iris/IPM.v
- Sec. 7.2, Definition of *fancy update* --> `IUpd` at iris/IPM.v
- Sec. 7.2, example --> Provided in imp/example/Stealing.v
- Sec. 7.3, accessor pattern --> `SubIProp` at iris/IPM.v

Sec. 8 A CONCRETE INSTANCE OF MRA
- Fig.13 --> Collected in FreeSim/Behavior.v
- The *core* operator --> `core_h` at ems/ModSemE.v
- *findDef* --> `prog: callE ~> itree Es` at ems/ModSem.v
- Theorem 8.1 --> Proved by `ModSem_MRA` at ems/ModSemFacts.v

## Additional materials
Integrating conditional refinement into RCL
- *wrapper modality* --> `Wrap` in iris/IPM.v
- Rules for the wrapper modality --> Module `WA` in lib/Algebra.v
- *Conditional refinement.* --> `CondRefines` in iris/IPM.v
- An example involving Rpt --> Section `CCR` in imp/example/Repeat.v
