constructor
intro h
intro x
intro h1
intro y
intro h2
have h3: y ∈ ⋂₀F := h h2
exact h3 x h1
intro h
intro x
intro h1
rw [mem_sInter]
intro t h2
have h3 : A ⊆ t := h t h2
exact h3 h1
