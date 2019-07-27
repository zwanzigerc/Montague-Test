# Montague-Test

This repository is a demonstration of how to apply the proof assistant Agda-flat (https://github.com/agda/agda/tree/flat) 
to natural language, in particular as a framework for computational Montague semantics. It provides logical forms in 
Agda-flat for the Montague Test sentence suite (Morrill and Valentín 2016).

It is a companion repository to the paper

Zwanziger, Colin. (2019). "Dependently-Typed Montague Semantics in the Proof Assistant Agda-flat." In Proceedings of the 16th 
Meeting on the Mathematics of Language. Philippe de Groote, Frank Drewes, and Gerald Penn, eds. https://www.aclweb.org/anthology/papers/W/W19/W19-5704/. Association for Computational Linguistics Anthology.

The file Flat.agda formalizes enough of the theory of the comonadic operator ♭ for the purposes of the Montague Test.

The file MontagueTest-Simple.agda gives logical forms for the Montague Test sentences. These are simpler and more readable, 
if less felicitous, versions of those given in the paper. The difference is that, here, natural language propositions are 
interpreted as types that are not necessarily propositions in the sense of homotopy type theory.

The file Logic.agda formalizes enough of "logic in homotopy type theory" to instead interpret natural language propositions
as propositions in the sense of homotopy type theory.

The file MontagueTest-Official.agda gives such an interpretation, formalizing the logical forms given in the paper.
