/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.Main.ModelCompanion

/-!
# Complete proofs of the registration statements

This entrypoint imports the actual proofs of `T3.exists_bounded_nonamalgamation_witness`
and `T3.has_model_companion`. The independent specification lives in `Challenge`; Comparator
compares their statements and all definitions used in those statements across the two modules.

Paper-ID: main.bounded_witness, main.model_companion
TeX: T3_modelcompanion_v9.tex, `thm:main`, Theorem 3.3 and Corollary 3.4, lines 795–838.
-/
