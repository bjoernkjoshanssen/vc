import numpy as np
import itertools
import operator

def wordAccepted(word,A):
	start = np.matrix([[1],[0]])
	wordMatrix = reduce(
		operator.mul,
		[A[word[i]] for i in range(0, len(word))]
	)
	if (wordMatrix*start)[0][0]>0:
		return True
	return False

count = 0
wordsAccepteds = []
for a0 in itertools.product((0,1),repeat=4):
	A0 = np.matrix([[a0[0],a0[1]],[a0[2],a0[3]]])
	for a1 in itertools.product((0,1),repeat=4):
		count += 1
		A1 = np.matrix([[a1[0],a1[1]],[a1[2],a1[3]]])
		for acceptState in (0,1):
			A = (A0,A1,acceptState)
			wordsAccepted = set()
			for word in itertools.product((0,1),repeat=3):
				if wordAccepted(word,A):
					wordsAccepted.add(word)
			if not wordsAccepted in wordsAccepteds:
				wordsAccepteds += [wordsAccepted]
			#print count,wordsAccepted,len(wordsAccepted)
			#print count,len(wordsAccepted)
#print "The following sets of words of length 3 can be accepted using 2 states:"
#for setOfWords in wordsAccepteds:
#	print setOfWords

theWords = list(itertools.product((0,1),repeat=3))
maxSize = 0
for e1 in range(0, 8):
	for e2 in range(e1+1,8):
		for e3 in range(e2+1,8):
			for e4 in range(e3+1,8):
				for e5 in range(e4+1,8):
					toShatter = set([theWords[e1],theWords[e2],theWords[e3],theWords[e4],theWords[e5]])
					#print "Here are the possible intersections with " + str(toShatter)
					setOfCodes = set()
					for setOfWords in wordsAccepteds:
						currentInter = setOfWords & toShatter
						currentCode = 0
						currentBit = 0
						for myWord in itertools.product((0,1),repeat=3):
							if myWord in currentInter:
								currentCode += 2**currentBit
							currentBit += 1
						if not currentCode in setOfCodes:
							#print currentInter, currentCode
							setOfCodes.add(currentCode)
					#print setOfCodes
					if len(setOfCodes)>maxSize:
						print len(setOfCodes)
						maxSize = len(setOfCodes)
print "The greatest number of subsets of a set of 5 words of length 3 that can be accepted by 2-state automata is " + str(maxSize)