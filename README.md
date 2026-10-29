# Navier–Stokes — prova (Lean 4 / Mathlib)

Depende do enunciado em [`ShantiDraconis/clay-navier-stokes-statement`](https://github.com/ShantiDraconis/clay-navier-stokes-statement),
fixado no commit `28e33a0`. O alvo é `ClayNavierStokes.ClayA`, sem redefinição.

O prêmio é por UMA das quatro: `ClayA`, `ClayB`, `ClayC` ou `ClayD`. Troque o alvo conforme o caso. A disjunção não serve (`A_or_C` é tautologia).

Estado: sem prova. `OPEN_MATH = true`.

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms ClayNavierStokesProof.main` fixado
com `#guard_msgs` quando `main` existir.

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.

## Enunciados (A) e (C) do Formal Conjectures (cópia, Apache-2.0)

[`ClayNavierStokesProof/FCStatements.lean`](ClayNavierStokesProof/FCStatements.lean): cópia das
definições de [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures),
`FormalConjectures/Millenium/NavierStokes.lean`, commit `8bf45ed70d48b2b2a501de9c00b26bfa38c573ee`
(o mesmo citado pela OpenAI), sob a licença Apache-2.0 (cabeçalho mantido; texto em
[`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt)). As definições copiadas (`divergence`,
`InitialVelocityCondition(Decay)`, `ForceCondition(Decay)`, `NavierStokesExistenceAndSmoothness(Rn)`)
são idênticas ao original, só no namespace `ClayNavierStokesProof.FC` e com notações locais.
Os enunciados dos teoremas (A) e (C) de lá entram como definições:

- `FCExistenceR3 : Prop` — enunciado de `navier_stokes_existence_and_smoothness_R3` (A). **Em aberto.**
- `FCBreakdownR3 : Prop` — enunciado de `navier_stokes_breakdown_R3` (C).

O que NÃO é: nenhuma das duas é provada aqui; são enunciados. Origem: o texto também coincide com a
cópia do kernel ATK (`ATK/Externo/FCNavierStokes.lean`, espelho público `atk-math-core-public`
@ `ffc111a`) e com `NavierStokes/ComparatorDefinitions.lean` da OpenAI (`f9e8bc5`).

## Dicionário: objetos fixados ⟷ objetos do Formal Conjectures

[`ClayNavierStokesProof/FCBridge.lean`](ClayNavierStokesProof/FCBridge.lean), teoremas sem hipóteses:

- operadores nas fatias de funções lisas em `H = ℝ³ × [0,∞)`: `dx_eq`, `dt_eq`, `lap_eq`,
  `grad_eq`, `convect_eq`, `divx_eq` (os operadores `fderivWithin` do enunciado fixado são `fderiv`,
  `derivWithin` em `[0,∞)`, `Δ`, `gradient` e o traço usados pelo Formal Conjectures);
- `smoothDivFree_decay4_iff : SmoothDivFree u₀ ∧ Decay4 u₀ ↔ FC.InitialVelocityConditionDecay u₀`
  (expoente `K` natural ⟷ real);
- `forcing5_iff : Forcing5 f ↔ FC.ForceConditionDecay (fun x t => f (x, t))`;
- `goodSolutionR3_iff : GoodSolutionR3 ν u₀ f p u ↔ FC.NavierStokesExistenceAndSmoothnessRn ν u₀ (curry f) (curry u) (curry p)`
  (inclui energia `∫⁻ ≤ C` ⟷ `MemLp _ 2 ∧ ∫ < E`).

O que NÃO é: só tradução entre duas formalizações do mesmo enunciado; nenhuma estimativa de
Navier–Stokes. Origem: a direção "FC ⇒ fixado" vem de uma ponte escrita numa auditoria anterior; os
lemas de fatia seguem `ATK/IntegracaoFCNS.lean` §1–2 (kernel ATK, espelho público), reescritos para
os operadores fixados. As voltas (fixado ⇒ FC) das condições e da energia são novas.

## (A) e (C) fixados ⟺ (A) e (C) do Formal Conjectures; (C) condicional à prova da OpenAI

[`ClayNavierStokesProof/FCClay.lean`](ClayNavierStokesProof/FCClay.lean):

- `clayA_iff_fcExistenceR3 : ClayNavierStokes.ClayA ↔ FCExistenceR3` e
  `target_iff_fcExistenceR3 : Target ↔ FCExistenceR3` — o alvo deste repositório é exatamente o (A)
  do Formal Conjectures. Análogo, para o enunciado fixado, de `clayA_iff_fc` do kernel ATK
  (`ATK/IntegracaoFCNS.lean`). **(A) continua em aberto.**
- `clayC_iff_fcBreakdownR3 : ClayNavierStokes.ClayC ↔ FCBreakdownR3` (incondicional).
- `clayC_of_fcBreakdown : FCBreakdownR3 → ClayNavierStokes.ClayC` — **condicional a resultado
  externo**: `FCBreakdownR3` é o tipo do teorema `NavierStokes.Comparator.navier_stokes_breakdown_R3`
  de [`openai/NavierStokesAndEuler`](https://github.com/openai/NavierStokesAndEuler) (OpenAI, commit
  `f9e8bc5`, setembro de 2026; [artigo](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)).
  Aquele projeto usa Lean `v4.34.0-rc2` e outra Mathlib, e **não** é importado: a hipótese é uma
  `Prop` nomeada, não um axioma, e a prova da OpenAI não é verificada por este repositório.

O que NÃO é: não é prova de (C) nem de (A). Como a hipótese de `clayC_of_fcBreakdown` é equivalente
à conclusão (`clayC_iff_fcBreakdownR3`), o teorema só transporta o resultado externo para o
enunciado fixado. `OPEN_MATH = true` continua valendo para este repositório.

**(D) não é afirmado.** O (D) do Formal Conjectures (`navier_stokes_breakdown_periodic`, também da
OpenAI) só nega soluções com **pressão periódica** (errata do Clay). O `ClayNavierStokes.ClayD`
fixado nega soluções com qualquer pressão lisa (`GoodSolutionPer` não pede pressão periódica), o
que é mais forte; o (D) do Formal Conjectures não implica o (D) fixado por esta via.

## Axiomas

Todas as 33 declarações novas dependem só de `[propext, Classical.choice, Quot.sound]`, fixado com
`#guard_msgs` em [`ClayNavierStokesProof/Audit.lean`](ClayNavierStokesProof/Audit.lean) (importado
por último pela raiz).

Não portado do kernel ATK: a cadeia de enstrofia/critérios (`ATK/NSCriterio.lean`, `NSEnergia`,
`NSMild`, …) e as partes de `ATK/IntegracaoFCNS.lean` sobre o enunciado próprio do ATK (classe de
Schwartz, equação em `t > 0`, continuidade em `t = 0`): falam de objetos do ATK, não dos objetos
fixados, e não são necessárias para as equivalências acima.
