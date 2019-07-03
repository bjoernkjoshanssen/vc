wordLength = 6

import numpy as np
import itertools
import operator

def wordAccepted(word,A):
	start = np.matrix([[1],[0]])
	n = len(word)
	wordMatrix = reduce(
		operator.mul,
		[A[word[i]] for i in range(0, n)]
	)
	if (wordMatrix*start)[A[2]][0]>0:
		return True
	return False


#print np.matrix([[1,2],[3,4]])*np.matrix([[1],[0]])

#      from..
#     [    ]
#to.. [    ]

for wordLength in range(1, 10):
	print "*"*80
	count = 0
	wordsAccepteds = []
	for a0 in itertools.product((0,1),repeat=4):
		A0 = np.matrix([[a0[0],a0[1]],[a0[2],a0[3]]])  # to make it work with more states just need bigger matrices...
		for a1 in itertools.product((0,1),repeat=4):
			count += 1
			A1 = np.matrix([[a1[0],a1[1]],[a1[2],a1[3]]])
			for acceptState in (0,1):
				A = (A0,A1,acceptState)
				wordsAccepted = set()
				for word in itertools.product((0,1),repeat=wordLength):
					if wordAccepted(word,A):
						wordsAccepted.add(word)
				if not wordsAccepted in wordsAccepteds:
					wordsAccepteds += [wordsAccepted]
				#print count,wordsAccepted,len(wordsAccepted)
				#if wordsAccepted & set([(0,0,0),(0,0,1),(0,1,0),(0,1,1),(1,1,0)]) == set([(0,0,0),(0,0,1),(0,1,1),(1,1,0)]):
				#	print A
				#	print
				#	raise SystemExit
				#print count,len(wordsAccepted)
	#print "The following sets of words of length 3 can be accepted using 2 states:"
	#for setOfWords in wordsAccepteds:
	#	print setOfWords

	#theWords = list(itertools.product((0,1),repeat=wordLength))
	maxSize = 0
	for dimensionToCheck in range(0, 2**wordLength + 1):
		aCount = 0
		for toShatter in itertools.combinations(itertools.product((0,1),repeat=wordLength),dimensionToCheck):
			aCount += 1
			if aCount % 1000 == 0:
				print aCount
			#toShatter = set([theWords[i] for i in e])
			#print "Here are the possible intersections with " + str(toShatter)
			setOfCodes = set()
			for setOfWords in wordsAccepteds:
				currentInter = setOfWords & set(toShatter)
				currentCode = 0
				currentBit = 0
				for myWord in itertools.product((0,1),repeat=wordLength):
					if myWord in currentInter:
						currentCode += 2**currentBit
					currentBit += 1
				if not currentCode in setOfCodes:
					#print currentInter, currentCode
					setOfCodes.add(currentCode)
			#print setOfCodes
			#if len(setOfCodes) == 2**dimensionToCheck:
			#	print A
			#	print toShatter
			if len(setOfCodes)>maxSize:
				#print len(setOfCodes)
				maxSize = len(setOfCodes)
				if maxSize == 2**dimensionToCheck:
					print str(toShatter) + " witnesses that "
					break
		print (
			"the greatest number of subsets of a set of " + str(dimensionToCheck)
			+ " words of length " + str(wordLength)
			+ " that can be accepted by 2-state automata is " + str(maxSize) + " <= " + str(2**dimensionToCheck)
		)
		print
		if maxSize < 2**dimensionToCheck:
			print "VC-dim = " + str(dimensionToCheck - 1)
			break