intro x h
have h3: x ∈ B:= h1 h
have h4: x ∈ C := h2 h
exact And.intro h3 h4
