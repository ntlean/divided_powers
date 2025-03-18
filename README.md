# Divided Powers

This repository contains source code for the article "A Formalization of Divided Powers in Lean", [submitted to ITP 2025]([https://popl24.sigplan.org/home/CPP-2024](https://icetcs.github.io/frocos-itp-tableaux25/itp/)). 
The code runs over Lean 4 (v4.18.0-rc1) and Mathlib's version [951bd16](https://github.com/leanprover-community/mathlib4/commit/951bd16d55870f47b2e2cd98c794f933e29bd2b5) (March 18, 2025).

Given an ideal $I$ in a commutative ring $A$, a divided power structure on $$I$$ is a collection of maps 
$`\{\gamma_n \colon I \to A\}_{n \in \mathbb{N}}`$,
subject to axioms that imply that it behaves like the family $`\{x \mapsto \frac{x^n}{n!}\}_{n \in \mathbb{N}}`$, but which can be defined even when division by factorials is not possible in $A$. 
Divided power structures have important applications in diverse areas of mathematics, including algebraic topology, number theory and algebraic geometry.

In this article we describe a formalization in Lean 4 of the basic theory of divided power structures, including divided power morphisms and sub-divided power ideals, and we provide several fundamental constructions, in particular quotients and sums. This constitutes the first formalization of this theory in any theorem prover.

As a prerequisite of general interest, we expand the formalized theory of multivariate power series rings, endowing them with a topology and defining evaluation and substitution of power series.

## File Authorship
Every file in this repository is new, original work of the anonymous paper authors.

## Installation instructions
The formalization has been developed over Lean 4 and its mathematical library Mathlib. For detailed instructions to install Lean, Mathlib, and supporting tools, visit the [Lean Community website](https://leanprover-community.github.io/get_started.html).

After installation, run the commands `git clone https://github.com/ntlean/divided_powers.git` to obtain a local copy of the repository and `lake exe cache get!` to download a compiled Mathlib. To open the project in VS Code, either run `path/to/divided_powers` on the command line, 
or use the "Open Folder" menu option to open the project's root directory. To compile the whole project locally, use the command `lake build`.
