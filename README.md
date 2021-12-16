
# Table of Contents

1.  [Introduction](#org14b34b3)
2.  [Short guide to the Coq mechanization](#org07a992a)
3.  ["Pencil and paper" omitted formalizations](#org7848e10)
    1.  [Backtranslation of target contexts into source ones](#orgef4af42)
        1.  [Context backtranslation](#org963e725)
        2.  [Declaration backtranslation](#orgc3d9401)
        3.  [Basic-blocks backtranslation](#org33dc66d)
        4.  [Command backtranslation](#org2668cc0)
        5.  [Jump/call backtranslation](#org1298ec2)
    2.  [Compiler](#org6ed8500)
        1.  [Compiling partial programs](#org0f73ec8)
        2.  [Compiling function defs](#orgfa4c82b)
        3.  [Compiling expressions](#orgdc64112)
    3.  [Proofs for the analyses](#org6be9e29)
        1.  [Source analysis](#org0c4cb13)
        2.  [Target analysis](#orge19f755)
4.  [References](#org9801505)


<a id="org14b34b3"></a>

# Introduction

This file serves as an index for our Coq mechanization and includes the parts
that were omitted from the Coq mechanization.


<a id="org07a992a"></a>

# Short guide to the Coq mechanization

-   The complete mechanization of the formal framework presented in Section IV
    is in the file `Framework.v`
-   The case study is splitted among the following files in the example folder:
    -   `Common.v` includes some domains common to all languages as well as the
        definition of our observables (denoted as Σ in the paper)
    -   `Src.v` and `ASrc.v` include the mechanization of the source language
        presented in the paper (μC) and its abstract version
    -   Similarly, `Trg.v` and `ATrg.v` implement the target language presented
        in the paper (μA) and its abstract version (history expressions)
    -   In `CaseStudy.v` we bring everything together and
        -   Specialize the framework of `Framework.v` to the specific case of
            call/return observables and the above languages
        -   The source analysis is defined trivially starting from the
            concrete and abstract source languages
        -   Also, the target analysis (a type and effect system) is implemented in
            [TrgAnalysis.v] and shown to adhere to our framework
        -   Statements of our pencil and paper proofs are reported (see below for
            the actual proofs)
-   The mechanization works with Coq 8.11.1. Checking it is just a matter of
    launching
    
        make clean; make all
    
    in the root directory of the material.


<a id="org7848e10"></a>

# "Pencil and paper" omitted formalizations


<a id="orgef4af42"></a>

## Backtranslation of target contexts into source ones

As said in the paper we backtranslate a target context into a source one
that simulates the execution of the target code.
For that, we use a `regᵤ` buffer (storing registers of compartment `u`) and a
`mem` buffer (storing memory values, globally).
For simplicity we assume them to be declared beforehand and we let mem to be
a global buffer (though no global buffers are admitted in μC we can simulate
them using a compartment acting as a manager).

Also, let

1.  bt<sub>d</sub> ( `d*` ) ≜ bt<sub>d</sub> (`d1`) &#x2026; bt<sub>d</sub> (`dn`)  if `d*` = `d1 ... dn`
2.  bt<sub>b</sub> ( `b*` ) ≜ bt<sub>b</sub> (`b1`) &#x2026; bt<sub>b</sub> (`bn`)  if `b*` = `b1 ... bn`
3.  bt<sub>c</sub> ( `c*` ) ≜ bt<sub>c</sub> (`c1`) `;` &#x2026; `;` bt<sub>c</sub> (`cn`)  if `c*` = `c1 ... cn`

**Note** the backtranslation is performed statically, thus all recursive calls
to backtranslation function(s) will not be present in the actual
backtranslated context.


<a id="org963e725"></a>

### Context backtranslation

-   bt<sub>C</sub> ( `u : i { d* } C` ) ≜ `comp u : i {` btᵘ<sub>d</sub> ( `d*` ) `}` bt<sub>C</sub> (`C`)
-   bt<sub>C</sub> ( `·` ) ≜ `·`


<a id="orgc3d9401"></a>

### Declaration backtranslation

-   btᵘ<sub>d</sub> ( `define f { b* }` ) ≜  `fun f { regᵤ[com] := arg[0]; u.f#entry (0) }` bt<sup>u,f</sup><sub>b</sub> (`b*`)

-   Note that we setup the parameter as expected by target code (i.e., in the com register, assumed to be a fixed constant known beforehand).


<a id="org33dc66d"></a>

### Basic-blocks backtranslation

-   bt<sup>u,f</sup><sub>b</sub> ( `ℓ: c* j` ) ≜ `fun f#ℓ {` btᵘ<sub>c</sub> (`c*`) `;` bt<sup>u,f</sup><sub>j</sub> (`j`) `}`

-   The idea is that each label (entry included) is backtranslated to an "ancillary" function, that will be called upon jumps


<a id="org2668cc0"></a>

### Command backtranslation

-   btᵘ<sub>c</sub> (`nop`) ≜ `42`  // Any value will do
-   btᵘ<sub>c</sub> (`const v r`) ≜ `regᵤ[r] := v`
-   btᵘ<sub>c</sub> (`mov rs rd`) ≜ `regᵤ[rd] := regᵤ[rs]`
-   btᵘ<sub>c</sub> (`ld rs rd`) ≜ `regᵤ[rd] := mem[regᵤ[rs]]`
-   btᵘ<sub>c</sub> (`st rs rd`) ≜ `mem[regᵤ[rd]] := regᵤ[rs]`
-   btᵘ<sub>c</sub> (`op r1 r2 rd`) ≜ `regᵤ[rd] := regᵤ[r1] op regᵤ[r2]`


<a id="org1298ec2"></a>

### Jump/call backtranslation

-   bt<sup>u,f</sup><sub>j</sub> (`halt`) ≜ `halt`
-   bt<sup>u,f</sup><sub>j</sub> (`bnz r ℓ1 ℓ2`) ≜ `if regᵤ[r] then u.f#ℓ1 (0) else u.f#ℓ2 (0)`
-   bt<sup>u,f</sup><sub>j</sub> (`jmp ℓ`) ≜ `u.f#ℓ (0)`
-   bt<sup>u,f</sup><sub>j</sub> (`call u'.f' ℓr`) ≜ `u'.f' (regᵤ[com]); u.f#ℓr (0)`
-   bt<sup>u,f</sup><sub>j</sub> (`ret`) ≜ `arg[0] := regᵤ[com]`

**Comments**

-   `bnz` and `jmp` are backtranslated to (conditional) calls to "ancillary"
    functions inside the module itself: this works since target-level jumps
    are just intra-function and intra module (see semantics of jumps in
    `Trg.v`)
-   The call parameters for `bnz` and `jmp` backtranslations are dummy and not used
    since we are not calling the function itself and thus we do not setup the
    `regᵤ[com]` buffer entry
-   The `ret` instruction is dual to the function declaration backtranslation, thus we need to move the
    return value to `arg[0]` (as expected by the source language semantics).


<a id="org6ed8500"></a>

## Compiler

The compiler takes a partial source program and produces a partial target
one.
Ours is heavily inspired by that proposed in [CSF'16], which we report below
with our changes.
For simplicity, we assume:

-   `T = [s, e)` to be the interval in which code will reside
-   each module `u` to have a constant `SB_u` equal to the base of its stack in
    memory
-   each buffer `u.b` to have a constant `BA_u_b` denoting its base address in
    memory
-   a register `r_one` always carrying `1`; `r_com` to be the register for parameter
    passing; `r_aux~/~r_aux2` to be auxiliary registers; `r_sp` to be the register
    storing the current (local) stack pointer


<a id="org0f73ec8"></a>

### Compiling partial programs

`〚 comp Main : IMain { d* } 〛 ≜ Main : IMain { 〚 d* 〛 }`


<a id="orgfa4c82b"></a>

### Compiling function defs

The module here is fixed and equal to Main.

    〚 fun f { e } 〛 ≜
        define f {
            ℓ_entry:
               // load the stack pointer
               const SB_MAIN r_sp
               ld r_sp r_sp
               // store the argument passed in r_com in memory
               const BA_MAIN_ARG r_aux
               st r_com r_aux
               // compilation of the body
               〚 e 〛
               jmp ℓ_trailer
            ℓ_trailer:
                // store the stack pointer
                const (SB_MAIN - 1) r_aux
                st r_sp r_aux
                const 0 r_i // forall i except for r_i = r_com
                ret
        }


<a id="orgdc64112"></a>

### Compiling expressions

    〚 v 〛 ≜ const v r_com
    
    〚 e1 op e2 〛, op ≠ ; ≜
        〚 e1 〛
        // push r_com
        add r_sp r_one r_sp
        st r_com r_sp
        〚 e2 〛
        // pop into r_aux
        ld r_sp r_aux
        sub r_sp r_one r_sp
        op r_aux r_com r_com
    
    〚 e1; e2 〛 ≜
        〚 e1 〛
        〚 e2 〛
    
    〚 if e then e1 else e2 〛 ≜
            〚 e 〛
             bnz r_com ℓ1 ℓ2 // ℓ1 and ℓ2 fresh for the current function
        ℓ1: 〚 e1 〛
             jmp ℓe // ℓe fresh for the current function
        ℓ2: 〚 e2 〛
             jmp ℓe
        ℓe: nop
    
    〚 b[e] 〛 ≜
            〚 e 〛
            const BA_MAIN_b r_aux
            add r_aux r_com r_aux
            ld r_aux r_com
    
    〚 b[e] := e1 〛 ≜
            〚 e 〛
            const BA_MAIN_b r_aux
            add r_aux r_com r_aux
            // push r_aux
            add r_sp r_one
            st r_aux r_sp
            〚 e1 〛
            // pop the stack value in r_aux
            ld r_sp r_aux
            sub r_sp r_one
            // store the result
            st r_com r_aux
    
    〚 u.f(e) 〛 ≜
            〚 e 〛
            // load arg[0] value in r_aux
            const BA_MAIN_ARG r_aux
            ld r_aux r_aux
            // store the loaded value on the stack
            add r_sp r_one
            st r_aux r_sp
            // store the old stack pointer
            const (SB_MAIN - 1) r_aux
            st r_sp r_aux
            const 0 r_i // forall i except for r_i = r_com
            // perform the call
            call u.f ℓr // ℓr fresh in the function
        ℓr: // restore the old stack pointer
            const 1 r_one
            const (SB_MAIN - 1) r_sp
            ld r_sp r_sp
            // pop the old argument into r_aux
            ld r_sp r_aux
            sub r_sp r_one r_sp
            // store it in the buffer, for futher use
            const BA_MAIN_ARG r_aux2
            st r_aux r_aux2
    
    〚 halt 〛 ≜ halt


<a id="org6be9e29"></a>

## Proofs for the analyses


<a id="org0c4cb13"></a>

### Source analysis

Let ⦇ · ⦈<sub>S</sub> be the source analysis with parameters k ∈ N and TestSet.

**Theorem (Source analysis is complete).** beh( ⦇ W ⦈<sub>S</sub> ) ⊆ beh(W).

**Proof.**
 Let t ∈ beh( ⦇ W ⦈<sub>S</sub> ).     
 By definition, the analysis extracts a t of length up to k from beh(W), so
 a trace t' that extends t must belong to beh(W).
 Finally, since beh is prefix-closed, it easily follows that also t ∈ beh(W) as requested. ∎


<a id="orge19f755"></a>

### Target analysis

Let ⦇ · ⦈<sub>T</sub> be the target analysis of `TrgAnalysis.v` (we omit T when clear from the context).

**Theorem (Target analysis is linear).** ∀ C, P. beh( ⦇ C[P] ⦈ ) = beh(⦇ C ⦈ [ ⦇ P ⦈]).

**Proof.** Trivial, by defininition of ⦇ · ⦈ for whole programs. ∎

Informally, suppose to extend the target analysis to be able to analyse
runtime configurations.

**Lemma (Subject reduction).**

If

-   initial<sub>cfg</sub> W —t→\* (u, σ, mem, reg, pc) = cfg ∧
-   (ρ, aW) = initial<sub>cfg</sub> ⦇ W ⦈ ∧
-   ρ ⊢ aW —t→\* aW' ∧
-   (u, σ, mem, reg, pc) —o→ (u', σ', mem', reg', pc') = cfg' ∧
-   ⦇ cfg ⦈ = aW'

then ∃ aW'' such that ρ ⊢ aW' —ε&#x2026;ε.o→\* aW'' ∧ ⦇ cfg' ⦈ ~ aW''.

**Proof (sketch).**

We go by cases on i = decode(mem(pc)).

-   **i ∉ {ret, call u.f}** it means that the current instruction is neither a
    call or a ret. The theses follow trivially by choosing aW'' = aW'.
-   **i = call u.f**, thus o = u.f;
    Since ⦇ cfg ⦈ = aW', by definition of ⦇·⦈ we know that ρ ⊢ aW'
    —u.f→ aW'', as requested.
    For the same reason, ⦇ cfg' ⦈ corresponds to the continuation of
    the program (i.e., starts with the body of u.f) and thus equals to
    aW'' (due to the copy rule in the semantics of history expressions).
-   **i = ret** Mutatis mutandis the previous case. ∎

**Theorem (Target analysis is sound).** ∀ C, P. beh(C[P]) ⊆ beh( ⦇ C[P] ⦈ )

**Proof.**
 Easily follows by induction on the length of traces and from the above subject reduction lemma. ∎


<a id="org9801505"></a>

# References

[CSF'16] Juglaret et al., Beyond Good and Evil: Formalizing the Security
Guarantees of Compartmentalizing Compilation, CSF 2016

