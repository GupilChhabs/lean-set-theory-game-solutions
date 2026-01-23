intro x h2
rw [mem_union]
by_cases hA : x∈ A
left
exact hA
right
rw [mem_sInter]
intro t h3
have h4 := h1 t h3
rw [mem_sInter] at h2
have h5 := h2 (A∪t) h4
rcases h5 with h5a|h5b
by_contra h6
exact hA h5a
exact h5b
