intro x h
have h3: x ∈ A ∪ C
left
exact h
have h4 : x ∈ B ∪ C := h1 h3
rcases h4 with h4a|h4b
exact h4a
have h5: x ∈ A∩C
constructor
exact h
exact h4b
have h6: x∈ B ∩ C := h2 h5
exact h6.left
