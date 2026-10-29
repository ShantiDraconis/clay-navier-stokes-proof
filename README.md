# Navier–Stokes — prova (Lean 4 / Mathlib)

Depende do enunciado em [`ShantiDraconis/clay-navier-stokes-statement`](https://github.com/ShantiDraconis/clay-navier-stokes-statement),
fixado no commit `28e33a0`. O alvo é `ClayNavierStokes.ClayA`, sem redefinição.

O prêmio é por UMA das quatro: `ClayA`, `ClayB`, `ClayC` ou `ClayD`. Troque o alvo conforme o caso. A disjunção não serve (`A_or_C` é tautologia).

Estado: sem prova. `OPEN_MATH = true`.

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms ClayNavierStokesProof.main` fixado
com `#guard_msgs` quando `main` existir.

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.
