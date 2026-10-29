import ClayNavierStokesProof.Main
import ClayNavierStokesProof.FCBridge

/-!
# (A) e (C) fixados ⟺ (A) e (C) do Formal Conjectures

Com o dicionário de `FCBridge.lean`:

* `clayA_iff_fcExistenceR3 : ClayNavierStokes.ClayA ↔ FCExistenceR3` (incondicional). O alvo
  `Target` deste repositório é exatamente o (A) do Formal Conjectures. **(A) continua aberto.**
* `clayC_iff_fcBreakdownR3 : ClayNavierStokes.ClayC ↔ FCBreakdownR3` (incondicional).
* `clayC_of_fcBreakdown : FCBreakdownR3 → ClayNavierStokes.ClayC` — **condicional a um resultado
  externo** (a prova da OpenAI de `navier_stokes_breakdown_R3`, ver a docstring de
  `FCBreakdownR3`). Como a hipótese é equivalente à conclusão, este teorema é só uma tradução de
  enunciado: todo o conteúdo matemático está na prova externa, que não é verificada aqui.

O que NÃO segue: o (D) fixado (`ClayNavierStokes.ClayD`). O (D) do Formal Conjectures
(`navier_stokes_breakdown_periodic`, também provado pela OpenAI) nega soluções cuja **pressão** é
periódica (errata do Clay); o (D) fixado nega soluções com qualquer pressão lisa (`GoodSolutionPer`
não exige pressão periódica), que é uma afirmação mais forte. Nada sobre (D) é afirmado aqui.

Ligação com o kernel ATK: `ATK/IntegracaoFCNS.lean` prova `clayA_iff_fc` para o enunciado (A) do
próprio ATK (`ClayStatementA modeloNS`, dado inicial na classe de Schwartz, equação para `t > 0`);
`clayA_iff_fcExistenceR3` é o análogo para o enunciado fixado, com prova direta pelo dicionário
(a passagem por continuidade em `t = 0` do ATK não é necessária, porque o enunciado fixado impõe a
equação em `t ≥ 0` com derivadas em `H`).

`OPEN_MATH = true`.
-/

namespace ClayNavierStokesProof

open ClayNavierStokes

/-- **(A) fixado ⟺ (A) do Formal Conjectures**, sem hipóteses. Nenhum dos dois lados é provado:
a existência global suave em `ℝ³` (alternativa (A) do Clay) continua em aberto. -/
theorem clayA_iff_fcExistenceR3 : ClayA ↔ FCExistenceR3 := by
  constructor
  · intro h nu hnu u₀ hu₀
    obtain ⟨hdiv, hdec⟩ := (smoothDivFree_decay4_iff u₀).mpr hu₀
    obtain ⟨p, u, hsol⟩ := h nu hnu u₀ hdiv hdec
    exact ⟨_, _, fcSolution_of_goodSolutionR3 (f := 0) hsol⟩
  · intro h ν hν u₀ hdiv hdec
    obtain ⟨v, p, hsol⟩ := h ν hν u₀ ((smoothDivFree_decay4_iff u₀).mp ⟨hdiv, hdec⟩)
    exact ⟨fun z => p z.1 z.2, fun z => v z.1 z.2,
      goodSolutionR3_of_fcSolution (f := 0) hsol⟩

/-- O alvo deste repositório é o (A) do Formal Conjectures. -/
theorem target_iff_fcExistenceR3 : Target ↔ FCExistenceR3 := clayA_iff_fcExistenceR3

/-- **(C) fixado ⟺ (C) do Formal Conjectures**, sem hipóteses. -/
theorem clayC_iff_fcBreakdownR3 : ClayC ↔ FCBreakdownR3 := by
  constructor
  · intro h nu hnu
    obtain ⟨u₀, f, hdiv, hdec, hf, hno⟩ := h nu hnu
    refine ⟨u₀, fun x t => f (x, t), (smoothDivFree_decay4_iff u₀).mp ⟨hdiv, hdec⟩,
      (forcing5_iff f).mp hf, ?_⟩
    rintro ⟨v, p, hsol⟩
    exact hno ⟨fun z => p z.1 z.2, fun z => v z.1 z.2, goodSolutionR3_of_fcSolution hsol⟩
  · intro h ν hν
    obtain ⟨u₀, f, hu₀, hf, hno⟩ := h ν hν
    obtain ⟨hdiv, hdec⟩ := (smoothDivFree_decay4_iff u₀).mpr hu₀
    refine ⟨u₀, fun z => f z.1 z.2, hdiv, hdec, (forcing5_iff _).mpr hf, ?_⟩
    rintro ⟨p, u, hsol⟩
    exact hno ⟨_, _, fcSolution_of_goodSolutionR3 hsol⟩

/-- **(C) fixado, condicional ao (C) do Formal Conjectures.**

A hipótese `FCBreakdownR3` é o enunciado de `navier_stokes_breakdown_R3`
(`google-deepmind/formal-conjectures`, `FormalConjectures/Millenium/NavierStokes.lean` @ `8bf45ed`),
cuja prova formal é o teorema `NavierStokes.Comparator.navier_stokes_breakdown_R3` de
[`openai/NavierStokesAndEuler`](https://github.com/openai/NavierStokesAndEuler) (OpenAI, commit
`f9e8bc5b38b6e212696e8a30e3e91517af887bbd`, setembro de 2026; artigo "Finite time blowup for
Navier–Stokes", https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf).
Esse projeto (Lean `v4.34.0-rc2`, outra Mathlib) **não** é importado: a hipótese é uma `Prop`
nomeada, não um axioma, e a prova externa não é verificada por este repositório.

Atenção: pela equivalência `clayC_iff_fcBreakdownR3`, a hipótese é equivalente à conclusão. Este
teorema apenas transporta o resultado externo para o enunciado fixado; não contém prova de (C). -/
theorem clayC_of_fcBreakdown (h : FCBreakdownR3) : ClayC :=
  clayC_iff_fcBreakdownR3.mpr h

end ClayNavierStokesProof
