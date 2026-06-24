
def flatten_str_list(l: list[str])-> str:
    """
    Faltten a list of str `l` to get one string.\n
    Example :\n
        flatten_str_list(["a", "b"]) ---> "ab".
    """
    res = ""
    for e in l:
        res += e + '\n'
    return res



def write_str_in_file(filename: str, text: str)-> None:
    with open(filename, 'w') as f:
        f.write(text)