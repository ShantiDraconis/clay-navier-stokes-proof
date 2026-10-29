/-
Copyright 2026 The Formal Conjectures Authors.

This file has been modified from its original form in the Formal Conjectures
project.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Enunciados (A) e (C) de Navier–Stokes do Formal Conjectures (cópia)

Fonte: [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures),
arquivo `FormalConjectures/Millenium/NavierStokes.lean`, commit
`8bf45ed70d48b2b2a501de9c00b26bfa38c573ee` (2026-07-27), licença Apache-2.0 (cabeçalho original
mantido acima; texto da licença em `LICENSES/Apache-2.0.txt`). É o mesmo commit citado pela OpenAI
em `NavierStokes/ComparatorDefinitions.lean` (`openai/NavierStokesAndEuler`, commit `f9e8bc5`).

Copiadas **sem mudar o significado**: as definições de que dependem as alternativas (A) e (C)
(divergência, condições sobre o dado inicial e a força com decaimento, estruturas de solução em
`ℝⁿ`). Mudanças só de forma:

* namespace `ClayNavierStokesProof.FC` (lá: `NavierStokes`);
* as notações `ℝ^n`, `ℝ³` são locais (lá: `scoped[EuclideanGeometry]` em `FormalConjecturesForMathlib`)
  e `∇⬝` é local (lá: global);
* `import FormalConjecturesUtil` trocado pelos módulos da Mathlib usados;
* não copiados: os atributos `category`/`AMS`, os lemas de API da divergência, as definições do caso
  periódico (`IsOnePeriodic`, `…Periodic`) e os quatro teoremas (A)–(D) com `sorry`;
* os enunciados dos teoremas (A) `navier_stokes_existence_and_smoothness_R3` e (C)
  `navier_stokes_breakdown_R3` entram, fechados universalmente, como as definições
  `FCExistenceR3 : Prop` e `FCBreakdownR3 : Prop`. Nenhuma das duas é provada aqui.

Conferido: o texto das definições copiadas é idêntico (exceto namespace/notação) ao da cópia do ATK
(`ATK/Externo/FCNavierStokes.lean`, kernel ATK, espelho público) e ao da OpenAI
(`NavierStokes/ComparatorDefinitions.lean` @ `f9e8bc5`).
-/

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Laplacian

namespace ClayNavierStokesProof.FC

local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {n : ℕ}

/--
The divergence $\nabla \cdot v$ of a vector field $v : \mathbb{R}^n \to \mathbb{R}^n$
at a point $x$, computed as the trace of the Jacobian matrix.

In coordinates, $\nabla \cdot v = \sum_i \partial v_i / \partial x_i$.

This is available as the notation `∇⬝ v`. If `v` is not differentiable at `x`, then
`fderiv` is the zero map, so this definition has the corresponding junk value $0$.
-/
noncomputable
def divergence (v : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ := (fderiv ℝ v x).trace ℝ (ℝ^n)

@[inherit_doc]
local notation "∇⬝" => divergence

/--
Basic conditions on initial velocity field for the Navier-Stokes equations
in $n$-dimensional space.

The initial velocity must be:
- Divergence-free (incompressibility condition: $\nabla \cdot u_0 = 0$)
- Smooth ($C^\infty$)

These conditions apply regardless of spatial dimension.
-/
structure InitialVelocityCondition (u₀ : ℝ^n → ℝ^n) : Prop where
  /-- The initial velocity field is divergence-free (equation 2).
      This is the incompressibility constraint for the fluid. -/
  div_free : ∀ x, ∇⬝ u₀ x = 0
  /-- The initial velocity field is smooth ($C^\infty$ in all variables). -/
  smooth : ContDiff ℝ ∞ u₀

/--
Initial velocity conditions for the Navier-Stokes problem on all of $\mathbb{R}^n$.

In addition to being smooth and divergence-free, the velocity must decay
faster than any polynomial at spatial infinity (condition 4 in Fefferman's paper).

This condition ensures the velocity field has finite energy and reasonable
behavior as $\lVert x \rVert \to \infty$.
-/
structure InitialVelocityConditionDecay (u₀ : ℝ^n → ℝ^n) : Prop extends
    InitialVelocityCondition u₀ where
  /-- All derivatives of u₀ decay faster than any polynomial (condition 4).
  For any derivative order $m$ and any decay rate $K$, there exists a constant $C$
  such that $\lVert \partial^m u_0(x) \rVert \le C/(1+\lVert x \rVert)^K$. -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/--
The basic smoothness condition on the external forcing term.

The force $f(x,t)$ must be smooth ($C^\infty$) in both space and time variables
for $t \ge 0$.
-/
structure ForceCondition (f : ℝ^n → ℝ → ℝ^n) : Prop where
  /-- The force is smooth on $\mathbb{R}^n \times [0,\infty)$. -/
  smooth : ContDiffOn ℝ ∞ (↿f) (Set.univ ×ˢ Set.Ici 0)

/--
Force conditions for the Navier-Stokes problem on all of $\mathbb{R}^n$.

The force must be smooth and decay faster than any polynomial
in both space and time (condition 5 in Fefferman's paper).
-/
structure ForceConditionDecay (f : ℝ^n → ℝ → ℝ^n) : Prop extends ForceCondition f where
  /-- All derivatives of f decay faster than any polynomial in space and time (condition 5).
  For any derivative order $m$ and any decay rate $K$, there exists $C$ such that
  $\lVert \partial^m_{x,t} f(x,t) \rVert \le C/(1+\lVert x \rVert+t)^K$ for
  $t \ge 0$. -/
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + ‖x‖ + t) ^ K

/--
A solution (v, p) to the Navier-Stokes equations in n-dimensional space
with viscosity $\nu$, initial velocity $u_0$, and external force $f$.

This structure captures the core requirements for a solution:
1. The velocity and pressure satisfy the Navier-Stokes PDE (equation 1)
2. The velocity remains divergence-free for all time (equation 2)
3. The initial condition is satisfied (equation 3)
4. The solution is smooth ($C^\infty$) for all time $t \ge 0$ (equations 6, 11)
-/
structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop where
  /-- The Navier-Stokes equation (equation 1):
  $\partial v/\partial t + (v \cdot \nabla)v = \nu\Delta v - \nabla p + f$. -/
  navier_stokes : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  /-- Incompressibility constraint (equation 2): $\nabla \cdot v = 0$ for all
  $x$ and $t \ge 0$. -/
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0
  /-- Initial condition (equation 3): $v(x,0) = u_0(x)$ for all $x$. -/
  initial_condition : ∀ x, v x 0 = u₀ x
  /-- The velocity field is smooth ($C^\infty$) on $\mathbb{R}^n \times [0,\infty)$
  (conditions 6, 11). -/
  velocity_smooth : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)
  /-- The pressure field is smooth ($C^\infty$) on $\mathbb{R}^n \times [0,\infty)$
  (conditions 6, 11). -/
  pressure_smooth : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)

/--
A solution to the Navier-Stokes equations on all of $\mathbb{R}^n$ with appropriate
decay and energy bounds.

In addition to the basic solution properties, we require:
- The velocity is in $L^2$ at each time $t \ge 0$ (finite kinetic energy)
- The total energy remains bounded for all time (condition 7)
-/
structure NavierStokesExistenceAndSmoothnessRn
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  /-- The velocity is square-integrable at each time $t \ge 0$ (condition 7). -/
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  /-- The kinetic energy $\int \lVert v(x,t) \rVert^2\,dx$ remains uniformly bounded
  for all time (condition 7), where the integral is the Lebesgue integral. -/
  globally_bounded_energy : ∃ E, ∀ t ≥ 0, (∫ x : ℝ^n, ‖v x t‖ ^ 2) < E

end ClayNavierStokesProof.FC

namespace ClayNavierStokesProof

open FC

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Formal Conjectures (A)** — o enunciado do teorema `navier_stokes_existence_and_smoothness_R3`
de `FormalConjectures/Millenium/NavierStokes.lean` (commit `8bf45ed`; lá marcado
`research open`, prova `sorry`), fechado universalmente: existência global suave e de energia
limitada em `ℝ³`, sem força. **Problema em aberto**; não é provado aqui. -/
def FCExistenceR3 : Prop :=
  ∀ (nu : ℝ) (_ : nu > 0) (u₀ : ℝ³ → ℝ³) (_ : InitialVelocityConditionDecay u₀),
    ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ (f := 0) v p

/-- **Formal Conjectures (C)** — o enunciado do teorema `navier_stokes_breakdown_R3` de
`FormalConjectures/Millenium/NavierStokes.lean` (commit `8bf45ed`; lá prova `sorry`), fechado
universalmente: para todo `ν > 0` há dado inicial e força com decaimento sem solução global suave
de energia limitada em `ℝ³`.

**Resultado externo, NÃO provado neste repositório.** O enunciado de mesmo texto é o teorema
`NavierStokes.Comparator.navier_stokes_breakdown_R3` de
[`openai/NavierStokesAndEuler`](https://github.com/openai/NavierStokesAndEuler) (OpenAI,
commit `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`, 2026-09-10, arquivo
`NavierStokes/ComparatorSolution.lean`; artigo "Finite time blowup for Navier–Stokes",
https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf). Aquele
projeto usa Lean `v4.34.0-rc2` e outra Mathlib; ele não é importado nem recompilado aqui, e a
coincidência dos enunciados é textual (mesmas definições, mesma fonte), não verificada pelo
kernel através das duas versões da Mathlib. -/
def FCBreakdownR3 : Prop :=
  ∀ (nu : ℝ) (_ : nu > 0), ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p)

end ClayNavierStokesProof
