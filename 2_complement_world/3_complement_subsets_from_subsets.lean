intro x h2
rewrite [mem_compl_iff A x]
rewrite [mem_compl_iff] at h2
by_contra h3
have h4 : x ∈ B := h1 h3
exact h2 h4
