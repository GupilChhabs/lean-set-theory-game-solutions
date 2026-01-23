intro x h
rw [mem_sInter] at h
rw [mem_sInter]
intro t
intro h2
have h3: t∈ G := h1 h2
exact h t h3
