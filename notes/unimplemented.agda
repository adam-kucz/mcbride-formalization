
module Computation.Property
postulate
  sub-compute : ∀{m n tag}
    (σ : Sub m n)
    {e e' : expr-of-type tag m}
    (p : e ⇝ e')
    → ------------------------------
    subst σ e ⇝ subst σ e'

module Syntax.Context.Property
postulate
  sub-ctx-prop : ∀ {m n}
    (σ : Sub m n)
    {t : Holes}{tag}
    (C : Context (fmap [ id × _+ m ] t) tag m)
    (es : all-types (fmap [ id × _+ m ] t))
    → ------------------------------------------------------------------
    sub σ (fill-holes es C) == fill-holes (sub-all σ t es) (subc σ C)

module Subtyping
step-▷-preserves-~
  (~annot ([ π x: _ ]→ _) S' (λx, t~t') ` s~s')
  (lam-comp π t▷t″ S▷S″ T▷T″ s▷s″)
-- needs: S' == [ π x: S₀ ]→ T₀
