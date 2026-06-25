
def export_features(v: list)-> str:
    """
    Export, to a string format, features from a vector by looking at the types of each element of the vector.

    Example :
    For the vector `[0.2, 1.3, true, 5.1]`, the function must generate `F(float, float, bool, float)`
    Note that the only types supported are `float` and `bool`.
    """

    r = "F("

    for e in v:
        if isinstance(e, float):
            e_str = "float"
        elif isinstance(e, bool):
            e_str = "()"
        else:
            raise TypeError("features must be float or bool.")
        r += e_str + ", "
    
    # remove the last ", "
    if r[-2:] == ", ":
        r = r[:-2]
    
    r += ")"

    return r