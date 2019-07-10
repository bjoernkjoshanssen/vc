
def Savings():
    word = (0, 1, 1, 0, 1, 1)
    power = 1
    patternLength = 1
    for index in range(patternLength, len(word),patternLength):

        if (
            word[(index) - patternLength] != word[index]
            and index != len(word)-1
        ):
        patternLength += 1
        else:
            power+=1

    print("for pattern length " + patternLength + " power is " +(power/patternLength))
