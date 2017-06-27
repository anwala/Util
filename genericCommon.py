#Python3

import re
import time
import json
import hashlib
import requests
import os, sys, getopt

from bs4 import BeautifulSoup
from datetime import datetime
from subprocess import check_output

from random import randint
from os.path import dirname, abspath
from textstat.textstat import textstat
from boilerpipe.extract import Extractor
from urllib.parse import urlparse, quote, quote_plus

from selenium.webdriver.common.keys import Keys
from selenium.webdriver.common.action_chains import ActionChains


#local memeory project - start
def getLMPMultiLinksScaffoldDict(linksList, isLMP=False):

	for i in range(len(linksList)):
		lmpLinkDict = getLMPLinkScaffoldDict( linksList[i], isLMP=isLMP )
		linksList[i] = lmpLinkDict

	return linksList

def getLMPLinkScaffoldDict(link, title='', crawlDatetime='', snippet='', rank=0, page=0, isLMP=False):

	datetimeKeyName = 'datetime'
	if( isLMP ):
		datetimeKeyName = 'crawl-' + datetimeKeyName

	return {'link': link, 'title': title, datetimeKeyName: crawlDatetime, 'snippet': snippet, 'rank': rank, 'page': page}

def getISO8601Timestamp():
	return datetime.utcnow().isoformat() + 'Z'

def getLMPSourceScaffoldDict(nonLocalName=''):

	#for genSearchColSource definition, see single collection in http://www.localmemory.org/api/USA/02138/10/
	genSearchColSource = {}
	genSearchColSource['facebook'] = ''
	genSearchColSource['twitter'] = ''
	genSearchColSource['video'] = ''
	genSearchColSource['city-county-name'] = ''
	genSearchColSource['city-county-lat'] = 0
	genSearchColSource['city-county-long'] = 0
	genSearchColSource['country'] = ''
	genSearchColSource['miles'] = 0
	genSearchColSource['name'] = nonLocalName#suggestion precede non-Local sources with 'non-Local-' prefix
	genSearchColSource['open-search'] = []
	genSearchColSource['rss'] = []
	genSearchColSource['state'] = ''
	genSearchColSource['media-class'] = 'multiple media'
	genSearchColSource['media-subclass'] = ''
	genSearchColSource['website'] = ''

	return genSearchColSource

def getLMPNewsCollection(query=''):

	#for globalNewsCollection and globalNewsCollection.collection.links[i] definition see lmp.exn
	globalNewsCollection = {}
	globalNewsCollection['city-latitude'] = 0
	globalNewsCollection['city-longitude'] = 0
	globalNewsCollection['city'] = ''
	globalNewsCollection['collection'] = []#[{'source': genSearchColSource, 'links': []}]
	globalNewsCollection['country'] = ''
	globalNewsCollection['maximum-links-per-source'] = 0
	globalNewsCollection['query'] = query
	globalNewsCollection['self-lmg'] = ''
	globalNewsCollection['state'] = ''
	globalNewsCollection['timestamp'] = datetime.utcnow().isoformat() + 'Z'
	globalNewsCollection['zipcode'] = ''
	globalNewsCollection['self-collection'] = []

	return globalNewsCollection

def getSingleLMPColScaffoldDict(query, nonLocalName=''):

	genSearchColSource = getLMPSourceScaffoldDict(nonLocalName)
	globalNewsCollection = getLMPNewsCollection(query)
	globalNewsCollection['collection'].append( {'source': genSearchColSource, 'links': []} )

	'''
		globalNewsCollection['self-collection'] single instance format:
			{'deleted': True or False, 'search-uri': ''}
		globalNewsCollection.collection.links[i] single instance format:
			{
	          "crawl-datetime": "", 
	          "link": "http://deadspin.com/anti-dakota-access-pipeline-protesters-hang-enormous-ba-1790671349", 
	          "snippet": "Protesters calling for U.S. Bank to stop funding the Dakota Access Pipeline project hung a huge banner from the Vikings' stadium during\u00a0...", 
	          "title": "Anti-Dakota Access Pipeline Protesters Hang Enormous Banner ..."
	        }	
	'''

	return globalNewsCollection

def getMultipleLMPColScaffoldDict(countOfSources, query):
	import copy

	if( countOfSources < 1 ):
		return {}

	genSearchColSource = getLMPSourceScaffoldDict('Non-Local')
	globalNewsCollection = getLMPNewsCollection(query)

	for i in range(countOfSources):
		globalNewsCollection['collection'].append( {'source': copy.deepcopy(genSearchColSource), 'links': []} )

	return globalNewsCollection

#local memeory project - end

#command line params - start
def getOptValueDict(argv, optsArrayOfTups):
	#directive: place containing function in genericCommon.py
	if( len(optsArrayOfTups) == 0 ):
		print('\tgetOptValueDict() - Error: empty optsArrayOfTups')
		return {}

	#populate optStr and longOptArray - start
	optStr = ''
	longOptArray = []
	for argTup in optsArrayOfTups:
		
		if( len(argTup) != 2 ):
			print('\tgetOptValueDict() - Error: ensure optStr and optLongNameStr in tuple are present even though 1 may be empty')
			return {}

		if( len(argTup[0]) != 0 ):
			optStr = optStr + argTup[0]

		if( len(argTup[1]) != 0 ):
			longOptArray.append(argTup[1])
	#populate optStr and longOptArray - end

	#print optStr
	#print longOptArray
	#print
	optStr = optStr.strip()
	if( len(argv) == 0 or len(optStr) == 0 or len(longOptArray) == 0 ):
		return {}

	try:
		opts, args = getopt.getopt(argv, optStr, longOptArray)
	except:
		exc_type, exc_obj, exc_tb = sys.exc_info()
		fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
		print(fname, exc_tb.tb_lineno, sys.exc_info() )
		return {}

	optValueDict = {}
	for option, value in opts:	
		optValueDict[option] = value

	return optValueDict

def allKeysInDict(allKeys, sampleDict):

	for key in allKeys:
		if( key not in sampleDict ):
			return False

	return True

def allValuesForKeysInDictNonEmpty(allKeys, sampleDict):

	for key in allKeys:
		if( key in sampleDict ):
			if( len(sampleDict[key]) == 0 ):
				return False
		else:
			return False

	return True

def intTryParse(value):
	try:
		return int(value), True
	except ValueError:
		return value, False
#command line params - end

#url - start
def getCanonicalUrl(URL):
	from surt import handyurl
	from surt.IAURLCanonicalizer import canonicalize

	netloc = ''
	path = ''
	params = ''
	query = ''
	fragment = ''

	URL = URL.strip()
	if( len(URL)>0 ):
		
		canonicalURL = handyurl.parse(URL)
		canonicalURL = canonicalize(canonicalURL).getURLString()

		scheme, netloc, path, params, query, fragment = urlparse(canonicalURL)

	returnValue = netloc + path + params + query + fragment

	#normalize url
	if( returnValue[-1] == '/' ):
		returnValue = returnValue[:-1]

	return returnValue

def aylienURIClassTaxonoy(uri):

	print('\naylienURIClassTaxonoy() - start')

	uri = uri.strip()
	if( len(uri) == 0 ):
		return {}

	print('\turi:', uri)
	output = {}
	try:
		output = check_output(['curl', 'https://api.aylien.com/api/v1/classify/iab-qag', '-s', '-H', 'X-AYLIEN-TextAPI-Application-Key: a4f250f508265eeae6580fb34c9cc9fd', '-H', 'X-AYLIEN-TextAPI-Application-ID: e99b3c40', '-d', 'url='+uri])
		output = output.decode('utf-8')
		output = json.loads(output)
	except:
		genericErrorInfo()

	print('aylienURIClassTaxonoy() - end\n')
	return output
#url - end

#credit to: https://github.com/mapado/haversine/blob/master/haversine/__init__.py
def haversine(point1, point2, miles=True):
	from math import radians, cos, sin, asin, sqrt
	""" Calculate the great-circle distance between two points on the Earth surface.
	:input: two 2-tuples, containing the latitude and longitude of each point
	in decimal degrees.
	Example: haversine((45.7597, 4.8422), (48.8567, 2.3508))
	:output: Returns the distance bewteen the two points.
	The default unit is kilometers. Miles can be returned
	if the ``miles`` parameter is set to True.
	"""
	AVG_EARTH_RADIUS = 6371  # in km

	# unpack latitude/longitude
	lat1, lng1 = point1
	lat2, lng2 = point2

	# convert all latitudes/longitudes from decimal degrees to radians
	lat1, lng1, lat2, lng2 = map(radians, (lat1, lng1, lat2, lng2))

	# calculate haversine
	lat = lat2 - lat1
	lng = lng2 - lng1
	d = sin(lat * 0.5) ** 2 + cos(lat1) * cos(lat2) * sin(lng * 0.5) ** 2
	h = 2 * AVG_EARTH_RADIUS * asin(sqrt(d))
	if miles:
		return h * 0.621371  # in miles
	else:
		return h  # in kilometers

def workingFolder():
	return dirname(abspath(__file__)) + '/'

def createFolderAtPath(path):

	if( os.path.exists(path) == False ):
		try:
			check_output(['mkdir', path])
			#print('\tcreateFolderAtPath(): created new folder for col:', path)
		except:
			genericErrorInfo()
			print('\tcreateFolderAtPath(): created new folder for col:', path)

def getNowFilename():
	filename = str(datetime.now()).split('.')[0]
	return filename.replace(' ', '_').replace(':', '-')

def getNowTime():

	now = str(datetime.now()).split('.')[0]
	return now.replace(' ', 'T')

#dict - start
def getDictFromFile(filename):

	try:
		return getDictFromJson( readTextFromFile(filename) )
	except:
		genericErrorInfo()

	return {}

def getDictFromJson(jsonStr):

	try:
		return json.loads(jsonStr)
	except:
		genericErrorInfo

	return {}

def getStopwordsDict():

	stopwordsDict = {
		'i': True,
		'me': True,
		'my': True,
		'myself': True,
		'we': True,
		'our': True,
		'ours': True,
		'ourselves': True,
		'you': True,
		'your': True,
		'yours': True,
		'yourself': True,
		'yourselves': True,
		'he': True,
		'him': True,
		'his': True,
		'himself': True,
		'she': True,
		'her': True,
		'hers': True,
		'herself': True,
		'it': True,
		'its': True,
		'itself': True,
		'they': True,
		'them': True,
		'their': True,
		'theirs': True,
		'themselves': True,
		'what': True,
		'which': True,
		'who': True,
		'whom': True,
		'this': True,
		'that': True,
		'these': True,
		'those': True,
		'am': True,
		'is': True,
		'are': True,
		'was': True,
		'were': True,
		'be': True,
		'been': True,
		'being': True,
		'have': True,
		'has': True,
		'had': True,
		'having': True,
		'do': True,
		'does': True,
		'did': True,
		'doing': True,
		'a': True,
		'an': True,
		'the': True,
		'and': True,
		'but': True,
		'if': True,
		'or': True,
		'because': True,
		'as': True,
		'until': True,
		'while': True,
		'of': True,
		'at': True,
		'by': True,
		'for': True,
		'with': True,
		'about': True,
		'against': True,
		'between': True,
		'into': True,
		'through': True,
		'during': True,
		'before': True,
		'after': True,
		'above': True,
		'below': True,
		'to': True,
		'from': True,
		'up': True,
		'down': True,
		'in': True,
		'out': True,
		'on': True,
		'off': True,
		'over': True,
		'under': True,
		'again': True,
		'further': True,
		'then': True,
		'once': True,
		'here': True,
		'there': True,
		'when': True,
		'where': True,
		'why': True,
		'how': True,
		'all': True,
		'any': True,
		'both': True,
		'each': True,
		'few': True,
		'more': True,
		'most': True,
		'other': True,
		'some': True,
		'such': True,
		'no': True,
		'nor': True,
		'not': True,
		'only': True,
		'own': True,
		'same': True,
		'so': True,
		'than': True,
		'too': True,
		'very': True,
		'can': True,
		'will': True,
		'just': True,
		'don': True,
		'should': True,
		'now': True
	}
	
	return stopwordsDict
#dict - end


#html - start
def clean_html(html, method='python-boilerpipe'):
	

	if( method == 'python-boilerpipe' ):
		try:
			extractor = Extractor(extractor='ArticleExtractor', html=html)
			return extractor.getText()
		except:
			genericErrorInfo()
	elif( method == 'nltk' ):
		"""
		Copied from NLTK package.
		Remove HTML markup from the given string.

		:param html: the HTML string to be cleaned
		:type html: str
		:rtype: str
		"""

		# First we remove inline JavaScript/CSS:
		cleaned = re.sub(r"(?is)<(script|style).*?>.*?(</\1>)", "", html.strip())
		# Then we remove html comments. This has to be done before removing regular
		# tags since comments can contain '>' characters.
		cleaned = re.sub(r"(?s)<!--(.*?)-->[\n]?", "", cleaned)
		# Next we can remove the remaining tags:
		cleaned = re.sub(r"(?s)<.*?>", " ", cleaned)
		# Finally, we deal with whitespace
		cleaned = re.sub(r"&nbsp;", " ", cleaned)
		cleaned = re.sub(r"  ", " ", cleaned)
		cleaned = re.sub(r"  ", " ", cleaned)

		#my addition to remove blank lines
		cleaned = re.sub("\n\s*\n*", "\n", cleaned)

		return cleaned.strip()

	return ''
#html - end


#text - start
def getStrBetweenMarkers(inputStr, beginMarker, endMarker, startIndex=0):

	begIndex = inputStr.find(beginMarker, startIndex)
	
	if( begIndex != -1 ):
		begIndex += len(beginMarker)
		endIndex = inputStr.find(endMarker, begIndex)
		if( endIndex != -1 ):
			return inputStr[begIndex:endIndex].strip(), endIndex

	return '', -1


def isStopword(term):

	stopWordsDict = getStopwordsDict()
	if( term.strip().lower() in stopWordsDict ):
		return True
	else:
		return False


def isExclusivePunct(text):

	text = text.strip()
	for char in text:
		char = char.upper()
		if ord(char) >= 65 and ord(char) <= 90:
			return False

	return True

def getTopKTermsListFromText(text, k, minusStopwords=True):

	if( len(text) == 0 ):
		return []

	stopWordsDict = {}
	if( minusStopwords ):
		stopWordsDict = getStopwordsDict()

	topKTermDict = {}
	topKTermsList = []
	text = text.split(' ')

	for term in text:
		term = term.strip().lower()
		
		if( len(term) == 0 or term in stopWordsDict or isExclusivePunct(term) == True ):
			continue

		topKTermDict.setdefault(term, 0)
		topKTermDict[term] += 1

	sortedKeys = sorted( topKTermDict, key=lambda freq:topKTermDict[freq], reverse=True )

	if( k > len(sortedKeys) ):
		k = len(sortedKeys)

	for i in range(k):
		key = sortedKeys[i]
		topKTermsList.append((key, topKTermDict[key]))

	return topKTermsList

def avgReadabilityGrade(text):

	if( len(text) == 0 ):
		return -1

	avgGrade = 0
	avgGrade += textstat.flesch_kincaid_grade(text)
	avgGrade += textstat.coleman_liau_index(text)
	avgGrade += textstat.automated_readability_index(text)
	
	'''
	score = textstat.smog_index(text)
	score = textstat.linsear_write_formula(text)
	score = textstat.gunning_fog(text)
	'''

	return avgGrade/3

def getEntitiesFromText(plaintext, outfilename='tempNERTextToTag.txt'):
	#print('\ngetEntitiesFromText::getEntities() - start')

	if( len(plaintext) == 0 ):
		return []

	filePathToTag = './NER-TEXT/'
	try:
		createFolderAtPath(filePathToTag)
		filePathToTag += outfilename

		outfile = open(filePathToTag, 'w')
		outfile.write(plaintext)
		outfile.close()
	except:
		genericErrorInfo()
		return []
	
	entities = []
	try:
		#tagedText = check_output([workingFolder() + 'runJavaNER.sh'])
		tagedText = check_output(['java', '-mx500m', '-cp', workingFolder() + 'stanford-ner-3.4.jar', 'edu.stanford.nlp.ie.crf.CRFClassifier', '-loadClassifier', workingFolder() + 'english.muc.7class.distsim.crf.ser.gz', '-textFile', filePathToTag, '-outputFormat', 'inlineXML', '2>', '/dev/null'])
		tagedText = str(tagedText)

		entities = []
		INLINEXML_EPATTERN  = re.compile(r'<([A-Z]+?)>(.+?)</\1>')
		
		dedupDict = {}
		for match in INLINEXML_EPATTERN.finditer(tagedText):
			#print(match.group(0))
			#match.group(2) is entity
			#match.group(1) is class

			if( match.group(2) not in dedupDict ):
				entityAndClass = [match.group(2), match.group(1)]
				entities.append(entityAndClass)
				dedupDict[match.group(2)] = False

		#dict which separates classes of entities into different arrays - start
		#entities = (match.groups() for match in INLINEXML_EPATTERN.finditer(tagedText))
		#entities = dict((first, list(map(itemgetter(1), second))) for (first, second) in groupby(sorted(entities, key=itemgetter(0)), key=itemgetter(0)))
		#for entityClass, entityClassList in entities.items():
			#entities[entityClass] = list(set(entityClassList))
		#dict which separates classes of entities into different arrays - end

		#remove temp file - start
		check_output(['rm', filePathToTag])
		#remove temp file - end

	except:
		genericErrorInfo()

	#print('\ngetEntitiesFromText::getEntities() - end')
	return entities

def getRSentimentLabel(text):

	if( len(text) == 0 ):
		return ''

	try:
		output = check_output(['Rscript', workingFolder() + 'sentiment.r', text])
		output = output.decode('utf-8')
		
		if( output.find('positive') != -1 ):
			return 'pos'
		elif( output.find('negative') != -1 ):
			return 'neg'
		elif( output.find('neutral') != -1 ):
			return 'neutral'

	except:
		genericErrorInfo()

	return ''
#text - end


#file - start
def writeTextToFile(outfilename, text):

	try:
		outfile = open(outfilename, 'w')
		outfile.write(text)
		outfile.close()

		print('\twriteTextToFile(), wrote:', outfilename)
	except:
		genericErrorInfo()

def readTextFromFile(infilename):

	text = ''
	
	try:
		infile = open(infilename, 'r')
		text = infile.read()
		infile.close()
	except:
		genericErrorInfo()

	return text

def dumpJsonToFile(outfilename, dictToWrite):

	try:
		outfile = open(outfilename, 'w')
		json.dump(dictToWrite, outfile, ensure_ascii=False)#by default, ensure_ascii=True, and this will cause  all non-ASCII characters in the output are escaped with \uXXXX sequences, and the result is a str instance consisting of ASCII characters only. Since in python 3 all strings are unicode by default, forcing ascii is unecessary
		outfile.close()

		print('\twriteTextToFile(), wrote:', outfilename)
	except:
		genericErrorInfo()
#file - end

#twitter - start

#extract 863007411132649473 from 'https://twitter.com/realDonaldTrump/status/863007411132649473'
def getTweetIDFromStatusURI(tweetURI):

	tweetURI = tweetURI.strip()

	if( tweetURI[-1] == '/' ):
		tweetURI = tweetURI[:-1]

	if( tweetURI.find('status/') != -1 ):
		return tweetURI.split('status/')[1].strip()

	return ''


def extractVideoLinkFromTweet(tweetURI, driver=None):
	
	if( driver is None ):
		from selenium import webdriver
		driver = webdriver.Firefox()
		quitDriverFlag = True
	else:
		#since user sent driver, user is responsible for quitting driver
		quitDriverFlag = False

	try:
		twitterHTMLPage = seleniumLoadWebpage(driver, tweetURI, waitTimeInSeconds=2, closeBrowerFlag=quitDriverFlag)
		soup = BeautifulSoup(twitterHTMLPage, 'html.parser')
	except:
		genericErrorInfo()
		return ''

	videoLink = ''
	videoLinkContainer = soup.find(class_='AdaptiveMedia-videoContainer')

	if( videoLinkContainer is not None ):
		videoLinkContainer = videoLinkContainer.find('iframe')
		if( videoLinkContainer is not None ):
			if( videoLinkContainer.has_attr('src') ):
				
				videoLink = videoLinkContainer['src'].strip()
				queryIndex = videoLink.find('?embed_source=')
				if( queryIndex != -1 ):
					 videoLink = videoLink[:queryIndex].strip()
	
	return videoLink

	

def extractTweetsFromSearch(query='', uri='', maxTweetCount=100):

	query = query.strip()
	uri = uri.strip()

	if( len(query) == 0 and len(uri) == 0 ):
		return {}

	finalTweetsColDict = {}
	if( len(query) != 0 ):
		searchURI = 'https://twitter.com/search?f=tweets&q=' + quote_plus( query ) + '&src=typd'
		finalTweetsColDict = extractTweetsFromTweetURI(searchURI, maxTweetCount)
	else:
		for urlPrefix in ['url:', '']:
			searchURI = 'https://twitter.com/search?f=tweets&q=' + quote_plus( urlPrefix + uri ) + '&src=typd'
			finalTweetsColDict = extractTweetsFromTweetURI(searchURI, maxTweetCount)

			if( len(finalTweetsColDict) != 0 ):
				break
	
	return finalTweetsColDict

def extractTweetsFromTweetURI(tweetConvURI, tweetConvMaxTweetCount=100, noMoreTweetCounter=0):
	#patched use of Chrome with:https://archive.is/94Idt
	from selenium import webdriver

	tweetConvURI = tweetConvURI.strip()
	if( tweetConvURI.find('https://twitter.com/') != 0 ):
		return {}

	if( tweetConvMaxTweetCount < 1 ):
		tweetConvMaxTweetCount = 100

	try:
		driver = webdriver.Chrome(executable_path='/usr/bin/chromedriver')
		driver.set_window_size(840,380)
		#driver.maximize_window()
		driver.get(tweetConvURI)		
	except:
		genericErrorInfo()
		return {}

	finalTweetsColDict = {}
	extractTweetsMain(driver, finalTweetsColDict, tweetConvURI, tweetConvMaxTweetCount, noMoreTweetCounter)
	driver.quit()

	return finalTweetsColDict

def extractTweetsMain(driver, finalTweetsColDict, tweetConvURI, tweetConvMaxTweetCount=100, noMoreTweetCounter=0):

	print('\nextractTweetsMain()')

	tweetConvURI = tweetConvURI.strip()
	if( len(tweetConvURI) == 0 ):
		return

	if( tweetConvMaxTweetCount < 1 ):
		tweetConvMaxTweetCount = 100

	maxNoMoreTweetCounter = 2#2

	finalTweetsColDictPrevLen = len(finalTweetsColDict)
	print('\ttweets:', finalTweetsColDictPrevLen)
	print('\tnoMoreTweetCounter:', noMoreTweetCounter, 'of', maxNoMoreTweetCounter)
	randSleep()

	try:
		clickShowMore(driver)
		twitterHTMLPage = driver.page_source.encode('utf-8')
		tweets = twitterGetDescendants(twitterHTMLPage)

		for tweetId in tweets:

			if( tweetConvMaxTweetCount == 0 or len(finalTweetsColDict) < tweetConvMaxTweetCount ):
				#indicates unrestricted descendants length
				finalTweetsColDict[tweetId] = tweets[tweetId]
			else:
				print('\treached threshold');
				return

		if( finalTweetsColDictPrevLen == len(finalTweetsColDict) ):
			noMoreTweetCounter += 1
		else:
			noMoreTweetCounter = 0

		if( noMoreTweetCounter > maxNoMoreTweetCounter ):
			print('\tno more tweets, breaking')
			return

		scrollDown(driver, tweetConvURI)
		extractTweetsMain(driver, finalTweetsColDict, tweetConvURI, tweetConvMaxTweetCount, noMoreTweetCounter)
	except:
		genericErrorInfo()
	
def clickShowMore(driver):

	script = '''
		//revise when better understanding of DOM is established
		var showMoreSignature = ['[class="ThreadedConversation-moreRepliesLink"]', '[class="show-more-link"]'];
		for(var i = 0; i<showMoreSignature.length; i++)
		{
			var showMore = document.querySelectorAll(showMoreSignature[i]);
			for(var j=0; j<showMore.length; j++)
			{
				showMore[j].click();
			}
		}
	'''
	driver.execute_script(script)

	'''
		#executing this code led to attempt to click invisible elements which caused problems:
		is not clickable at point (510, 988). Other element would receive the click:
		StaleElementReferenceException'>, StaleElementReferenceException('stale element reference: element is not attached to the page document

		for className in ['ThreadedConversation-moreRepliesLink', 'show-more-link']:
			clickMoreElmts = driver.find_elements_by_class_name(className)
			for el in clickMoreElmts:
				try:
					el.click()
				except:
					genericErrorInfo()

			print('\tclickShowMore() - click:', len(clickMoreElmts))
	'''

def scrollDown(driver, uri, maxScroll=15, sleepSeconds=1):#15, 1
	
	if( uri.find('/status/') != -1 ):
		#this function doesn't work in firefox
		actions = ActionChains(driver)
		for i in range(maxScroll):
			actions.send_keys(Keys.SPACE).perform()
			print('\tscrollDown():', i, 'of', maxScroll)
			time.sleep(sleepSeconds)
	else:
		driver.execute_script('window.scrollTo(0, document.body.scrollHeight);')

def twitterGetDescendants(twitterHTMLPage):

	if( len(twitterHTMLPage) == 0 ):
		return {}

	tweetsDict = {};
	soup = BeautifulSoup(twitterHTMLPage, 'html.parser')
	tweets = soup.find_all(class_='tweet')

	for tweet in tweets:
		tweet = twitterGetTweetIfExist(tweet)
		if( len(tweet) != 0 ):
			tweetsDict[ tweet['data-tweet-id'] ] = tweet

	return tweetsDict

def isVideoAdaptiveMediaInTweet(tweetDivTag):

	try:
		imgAdaptiveMedia = tweetDivTag.find(class_='AdaptiveMedia-videoContainer')
		if( imgAdaptiveMedia is not None ):
			return True
	except:
		genericErrorInfo()
	
	return False

def twitterGetLinksFromTweetDiv(tweetDivTag):

	#grab expanded links from tweet-text - start
	tweetTextTag = tweetDivTag.find(class_='tweet-text')
	links = []
	expandedLinks = []

	try:
		if( tweetTextTag is not None ):
			links = tweetTextTag.find_all('a')
	except:
		genericErrorInfo()
		return []

	for link in links:
		if( link.has_attr('data-expanded-url') ):
			expandedLinks.append( link['data-expanded-url'].strip() )
	
	#grab expanded links from tweet-text - end


	#grab expanded links from adaptive media - start
	#adaptiveMediaDict = {'AdaptiveMedia-videoContainer': 'iframe', 'AdaptiveMedia-photoContainer': 'img'}
	adaptiveMediaDict = {'AdaptiveMedia-photoContainer': 'img'}
	
	#extract embeded images - start
	imgAdaptiveMedia = tweetDivTag.find(class_='AdaptiveMedia-photoContainer')
	if( imgAdaptiveMedia is not None ):
		imgAdaptiveMedia = imgAdaptiveMedia.find('img')
		if( imgAdaptiveMedia is not None ):
			if( imgAdaptiveMedia.has_attr('src') ):
				expandedLinks.append( imgAdaptiveMedia['src'].strip() )
	#extract embeded images - start
	#grab expanded links from adaptive media - end

	return expandedLinks

def twitterGetTweetIfExist(potentialTweetDiv):

	tweetDict = {};
	listOfTweetAttrs = ['data-tweet-id', 'data-name', 'data-screen-name']

	for attr in listOfTweetAttrs:
		if( potentialTweetDiv.has_attr(attr) ):
			tweetDict[attr] = potentialTweetDiv[attr]

	if( len(tweetDict) != len(listOfTweetAttrs) ):
		return {}

	tweetDict['tweet-text'] = ''
	tweetDict['tweet-time'] = ''
	tweetDict['tweet-links'] = []
	tweetDict['is-video-adaptive-present'] = False
	uniformAccessAttrs = ['data-conversation-id', 'data-mentions']

	tweetTag = potentialTweetDiv.find_all(class_='tweet-text')
	if( len(tweetTag) != 0 ):
		tweetDict['tweet-text'] = tweetTag[0].text

	tweetTag = potentialTweetDiv.find_all(class_='tweet-timestamp')
	if( len(tweetTag) != 0 ):
		if( tweetTag[0].has_attr('title') ):
			tweetDict['tweet-time'] = tweetTag[0]['title']

	for attr in uniformAccessAttrs:
		tweetDict[attr] = ''
		if( potentialTweetDiv.has_attr(attr) ):
			tweetDict[attr] = potentialTweetDiv[attr]

	tweetDict['tweet-links'] = twitterGetLinksFromTweetDiv(potentialTweetDiv)
	tweetDict['is-video-adaptive-present'] = isVideoAdaptiveMediaInTweet(potentialTweetDiv)
		
	return tweetDict


def isTweetPresent(soup):
	
	print('\t\tisTweetPresent()')
	tweets = soup.findAll('div', {'class': 'tweet'})
	if( len(tweets) == 0 ):
		return ''

	for tweet in tweets:
		if( tweet.has_attr('data-permalink-path') ):
			tweetPath = tweet['data-permalink-path'].strip()
			if( len(tweetPath) != 0 ):
		 	  	#print('\t\t\ttweetPath:', tweetPath)
				return tweetPath

	return ''

def isURIInTweet(link, driver=None, closeBrowserFlag=True):

	print('\nisURIInTweet()')

	urir = getURIRFromMemento(link)
	if( len(urir) != 0 ):
		print('\t\turi-r extracted from memento link, to be checked in tweet index')
		link = urir

	tweetPath = ''
	if( driver is None ):
		from selenium import webdriver
		driver = webdriver.Firefox()

	for urlPrefix in ['url:', '']:
		print('\t\turi prefix:', urlPrefix)
		uri = 'https://twitter.com/search?f=tweets&q=' + quote_plus(urlPrefix + link) + '&src=typd'
		htmlPage = seleniumLoadWebpage(driver, uri, waitTimeInSeconds=2, closeBrowerFlag=False)
		soup = BeautifulSoup( htmlPage, 'html.parser' )
		tweetPath = isTweetPresent(soup)

		if( len(tweetPath) != 0 ):
			break

	if( closeBrowserFlag == True ):
		driver.quit()

	return tweetPath
#twitter - end


#reddit - start
def redditSearch(query, subreddit='', maxPages='', extraFieldsDict={}):

	print('\nredditExpand() - start')

	query = query.strip()
	subreddit = subreddit.strip()
	maxPages = str(maxPages).strip()

	if( len(maxPages) == 0 ):
		maxPages = 0

	try:
		maxPages = int(maxPages)
	except:
		genericErrorInfo()
		maxPages = 0

	if( len(query) == 0 ):
		return []

	if( len(subreddit) != 0 ):
		subreddit = 'r/' + subreddit + '/'

	print('\tquery:', query)
	print('\tsubreddit:', subreddit)
	afterFlag = ''
	collection = []
	try:
		while True:
			print()
			redditQuery = 'https://www.reddit.com/' + subreddit +  'search.json?q=' + quote(query) + afterFlag
			redditJson = getDictFromJson( dereferenceURI(redditQuery) )
			
			print('\tredditQuery:', redditQuery)

			if( 'data' not in redditJson ):
				print('\tNo data key present')
				break

			redditJson = redditJson['data']

			for child in redditJson['children']:
				child = child['data']

				try:
					creationDate = datetime.utcfromtimestamp(child['created_utc'])
					#creationDate = creationDate.strftime("%b") + ' ' + creationDate.strftime('%m') + ', ' + creationDate.strftime('%Y')

					tempDict = {}
					tempDict['datetime'] = creationDate.isoformat()
					tempDict['link'] = child['url']
					tempDict['snippet'] = child['selftext']
					tempDict['title'] = child['title']
					
					tempDict['custom'] = {
						'author': child['author'], 
						'subreddit': child['subreddit'], 
						'permalink': 'https://www.reddit.com' + child['permalink']
					}

					for key, value in extraFieldsDict.items():
						tempDict[key] = value

					collection.append(tempDict)

					print('\t\tauthor:', child['author'])
					print('\t\ttitle:', child['title'])
					print('\t\tcreated:', creationDate)
					print('\t\turl:', child['url'])
					print('\t\tsubreddit:', child['subreddit'])
					print()
				except:
					genericErrorInfo()
			
			maxPages -= 1
			print('\tmaxPages:', maxPages)
			
			if( maxPages > 0 and redditJson['after'] ):
				afterFlag = '&after=' + redditJson['after']
			else:
				break
	except:
		genericErrorInfo()

	print('redditExpand() - end\n')
		
	return collection

def redditGetAllLinksFromCommentHTML(html):

	lastIndex = -1
	linksDict = {}
	while( True ):
		
		link, lastIndex = getStrBetweenMarkers(html, 'href="', '"', startIndex=lastIndex+1)
		if( lastIndex == -1 ):
			break
		else:
			if( link.find('http') == 0 ):
				linksDict[link] = True
	
	return list(linksDict.keys())

def redditRecursiveTraverseComment(payload, tabCount, detailsDict):

	'''
		verify recursion, count links, dedup links
		patch links with just scheme incomplete, move code to genericCommon? or reddit py
	'''
	tab = '\t' * tabCount
	#print(tab, 'redditRecursiveTraverseComment():')

	if( 'kind' in payload ):

		if( payload['kind'] == 'Listing' ):
			
			#print(tab, 'kind: Listing')
			if( 'data' in payload ):
				redditRecursiveTraverseComment( payload['data'], tabCount + 1, detailsDict )

		elif( payload['kind'] == 't3' ):
			
			#print(tab, 'kind: t3 (link)')
			if( 'data' in payload ):
				if( 'selftext_html' in payload['data'] ):
					detailsDict['links'] += redditGetAllLinksFromCommentHTML( payload['data']['selftext_html'] )

		elif( payload['kind'] == 't1' ):

			#print(tab, 'kind: t1 (comment)')
			detailsDict['comment-count'] += 1

			if( 'data' in payload ):

				if( 'body_html' in payload['data'] ):
					detailsDict['links'] += redditGetAllLinksFromCommentHTML( payload['data']['body_html'] )

			#comment with possible replies
				if( 'replies' in payload['data'] ): 
					if( len(payload['data']['replies']) != 0 ):
						redditRecursiveTraverseComment( payload['data']['replies'], tabCount + 1, detailsDict )#replies is a listing
	
	elif( 'children' in payload ):
		#print(tab, 'children')
		for child in payload['children']:
			redditRecursiveTraverseComment( child, tabCount + 1, detailsDict )

def redditGetLinksFromComment(commentURI):

	commentURI = commentURI.strip()
	if( len(commentURI) == 0 ):
		return []

	if( commentURI[-1] == '/' ):
		commentURI = commentURI[:-1]
	commentURI = commentURI + '.json'

	detailsDict = {'comment-count': 0, 'links': []}
	redditCommentJson = getDictFromJson(dereferenceURI(commentURI, 0))
	for commentThread in redditCommentJson:
		redditRecursiveTraverseComment( commentThread, 1, detailsDict )

	#print('comment:', detailsDict['comment-count'])
	#print( 'links:', len(detailsDict['links']) )
	return detailsDict['links']

#reddit - end


#wikipedia - start
def wikipediaGetExternalLinksDictFromPage(pageURI, maxSleepInSeconds=5):

	pageURI = pageURI.strip()
	if( len(pageURI) == 0 ):
		return []

	if( getDomain(pageURI).find('wikipedia.org') == -1 ):
		return []

	dedupDict = {}
	allLinksFromThisPage = []
	htmlPage = dereferenceURI(URI=pageURI, maxSleepInSeconds=maxSleepInSeconds)
	soup = BeautifulSoup( htmlPage, 'html.parser' )
	allCitations = soup.find( 'div', {'class':'reflist'} )

	if( allCitations is None ):
		return []

	allCitations = allCitations.findAll('li')

	if( allCitations is None ):
		return []

	for citation in allCitations:
		links = citation.findAll('a', {'rel':'nofollow'})
		for link in links:
			
			try:
				uri = link['href'].strip()
				if( uri[0] == '/' ):
					uri = 'http:' + uri

				if( uri not in dedupDict ):
					allLinksFromThisPage.append( {'link': uri, 'title': link.text.strip()} )
					dedupDict[uri] = True
			except:
				genericErrorInfo()

	return allLinksFromThisPage

def wikipediaGetExternalLinksFromPage(pageURI, maxSleepInSeconds=5):

	pageURI = pageURI.strip()
	if( len(pageURI) == 0 ):
		return []

	links = []
	linksDict = wikipediaGetExternalLinksDictFromPage(pageURI, maxSleepInSeconds)
	
	for linkDict in linksDict:
		links.append(linkDict['link'])

	return links
#wikipedia - end


#misc - start
def areAllKeysInDict(allKeys, sampleDict):

	for key in allKeys:
		if( key not in sampleDict ):
			return False

	return True

def areAllValuesForKeysInDictNonEmpty(allKeys, sampleDict):

	for key in allKeys:
		if( key in sampleDict ):
			if( len(sampleDict[key]) == 0 ):
				return False
		else:
			return False

	return True

def getOptValueDict(argv, optsArrayOfTups):
	#directive: place containing function in genericCommon.py
	if( len(optsArrayOfTups) == 0 ):
		print('Error: empty optsArrayOfTups')
		return {}

	#populate optStr and longOptArray - start
	optStr = ''
	longOptArray = []
	for argTup in optsArrayOfTups:
		
		if( len(argTup) != 2 ):
			print('Error: ensure optStr and optLongNameStr in tuple are present even though 1 may be empty')
			return {}

		if( len(argTup[0]) != 0 ):
			optStr = optStr + argTup[0]

		if( len(argTup[1]) != 0 ):
			longOptArray.append(argTup[1])
	#populate optStr and longOptArray - end

	#print optStr
	#print longOptArray
	#print
	optStr = optStr.strip()
	if( len(argv) == 0 or len(optStr) == 0 or len(longOptArray) == 0 ):
		return {}

	try:
		opts, args = getopt.getopt(argv, optStr, longOptArray)
	except:
		exc_type, exc_obj, exc_tb = sys.exc_info()
		fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
		print(fname, exc_tb.tb_lineno, sys.exc_info() )
		return {}

	optValueDict = {}
	for option, value in opts:	
		optValueDict[option] = value

	return optValueDict
#misc - end


#math - start
def normalizeList(dataList):

	if( len(dataList) == 0 ):
		return []	

	minVal = min(dataList)
	maxVal = max(dataList)
	dataList = [(x_i - minVal) / (maxVal - minVal) for x_i in dataList]
	
	return dataList
#math - end


#precondition: readingLevels are in grade range
def getReadabilityViaDiscretization(readingLevels):

	if( len(readingLevels) == 0 ):
		return -1

	readingLevelsDistDict = {}
	readingLevelsDistDict['low'] = {'sum': 0, 'count': 0}#range for grade 7 and below (inclusive)
	readingLevelsDistDict['mid'] = {'sum': 0, 'count': 0}#range for grade 8 to 12 (inclusive)
	readingLevelsDistDict['high'] = {'sum': 0, 'count': 0}#range for grade 13 and above
	
	for readingLevel in readingLevels:

		gradeRange = ''
		if( readingLevel <= 7 ):
			gradeRange = 'low'
		elif( readingLevel <= 12 ):
			gradeRange = 'mid'
		else:
			gradeRange = 'high'

		readingLevelsDistDict[gradeRange]['sum'] += readingLevel
		readingLevelsDistDict[gradeRange]['count'] += 1

	sortedKeys = sorted(readingLevelsDistDict, key=lambda gradeRange:readingLevelsDistDict[gradeRange]['count'], reverse=True)
	
	if( len(sortedKeys) != 0 ):
		gradeRange = sortedKeys[0]
		if( readingLevelsDistDict[gradeRange]['count'] != 0 ):
			return readingLevelsDistDict[gradeRange]['sum']/readingLevelsDistDict[gradeRange]['count']
	
	return -1

def getNLTKSentimentLabel(text):

	if( len(text) == 0 ):
		return {}

	try:
		output = check_output(['curl', '-s', '-d', 'text=' + text, 'http://text-processing.com/api/sentiment/'])
		output = output.decode('utf-8')
		return json.loads(output)
	except:
		genericErrorInfo()
		print('\toffending text:', output, '\n')
	
	return {}

#summary stats - start
def median(dataPoints, sortedFlag=True):

	#credit: https://github.com/Mashimo/datascience/blob/master/datascience/stats.py
	if not dataPoints:
		raise ValueError('no data points passed')

	if( sortedFlag ):
		dataPoints = sorted(dataPoints)

	mid = len(dataPoints) // 2  #floor division for int
	median = 0
	if (len(dataPoints) % 2 == 0):
		median = (dataPoints[mid-1] + dataPoints[mid]) / 2.0
	else:
		median = dataPoints[mid]

	return median

def quartiles(dataPoints, sortFlag=True):

	#credit: https://github.com/Mashimo/datascience/blob/master/datascience/stats.py
	if not dataPoints:
		raise ValueError('no data points passed')
	
	if( sortFlag ):
		dataPoints = sorted(dataPoints)

	mid = len(dataPoints) // 2 #floor division for int
	
	if (len(dataPoints) % 2 == 0):
		lowerQuartile = median(dataPoints[:mid], False)
		upperQuartile = median(dataPoints[mid:], False)
	else:
		lowerQuartile = median(dataPoints[:mid], False)
		upperQuartile = median(dataPoints[mid+1:], False)
	
	return [lowerQuartile, median(dataPoints, False), upperQuartile]

def fiveNumberSummary(numList):

	if( len(numList) == 0 ):
		return {}

	numList.sort()

	summaryStatsDict = {}
	quarts = quartiles(numList, False)

	summaryStatsDict['minimum'] = numList[0]
	summaryStatsDict['lower-quartile'] = quarts[0]
	summaryStatsDict['median'] = quarts[1]
	summaryStatsDict['upper-quartile'] = quarts[2]
	summaryStatsDict['maximum'] = numList[-1]

	return summaryStatsDict
#summary stats - end


# credit to: http://rosettacode.org/wiki/Levenshtein_distance
def LevenshteinDistance(s1,s2):
	if len(s1) > len(s2):
		s1,s2 = s2,s1

	distances = range(len(s1) + 1)
	for index2,char2 in enumerate(s2):

		newDistances = [index2+1]
		for index1,char1 in enumerate(s1):

			if char1 == char2:
				newDistances.append(distances[index1])
			else:
				newDistances.append(1 + min((distances[index1], distances[index1+1], newDistances[-1])))
		
		distances = newDistances
	return distances[-1]

def removePunctuations(term):

	translator = str.maketrans({key: None for key in string.punctuation})
	term = term.translate(translator)

	return term

def getSimilarityScore(str0, str1):

	str0 = str0.strip().lower()
	str1 = str1.strip().lower()

	if( len(str0) == 0 or len(str1) == 0 ):
		return 0

	maxLength = len(str0)
	if( len(str1) > maxLength ):
		maxLength = len(str1)

	distance = LevenshteinDistance(str0, str1)
	similarityScore = 1 - distance/float(maxLength)

	return similarityScore

def randSleep(maxSleepInSeconds=5):

	if( maxSleepInSeconds < 1 ):
		maxSleepInSeconds = 5

	sleepSeconds = randint(1, maxSleepInSeconds)
	print('\trandSleep(): sleep:', sleepSeconds)
	time.sleep(sleepSeconds)

def getSnippetForURI(uri):

	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''

	pagePageLinksDict = googleGetSERPResults(uri)
	for page, pageLinkDict in pagePageLinksDict.items():
		for linkDict in pageLinkDict:
			if( uri == linkDict['link'].strip() ):
				return linkDict['snippet'].strip()

	return ''


#google - start

def getQueryReciprocalRank(query, expectedLink, maxPageToVisit=3, seleniumFlag=False):
	
	print('\ngetQueryReciprocalRank() - start')

	query = query.strip()
	expectedLink = expectedLink.strip()

	if( len(query) == 0 or len(expectedLink) == 0 ):
		return 0

	allLinksCount = 0
	try:
		for page in range(1, maxPageToVisit+1):
			print('\tpage:', page, 'of', maxPageToVisit)
			print('\tquery:', query)
			print('\texpectedLink:', expectedLink)
			
			googleHTMLPage = googleGetHTMLPage(query, page, seleniumFlag)
			soup = BeautifulSoup( googleHTMLPage, 'html.parser' )
			linksDict = googleRetrieveLinksFromPage(soup)
			
			sortedKeys = sorted(linksDict, key=lambda x:linksDict[x]['rank'])
			for link in sortedKeys:
				
				allLinksCount += 1
				#print('\t\t', allLinksCount, link)
				
				if( link.find(expectedLink) == 0 ):
					
					RR = 1/allLinksCount
					
					print('\tFound')
					print('\tallLinksCount:', allLinksCount)
					print('\tRR:', RR)
					return RR

			if( len(linksDict) == 0 ):
				print('\tEmpty result, terminating')
				return 0
	except:
		genericErrorInfo()

	return 0
	print('\ngetQueryReciprocalRank() - end')

def googleGetHTMLPage(searchString, page, siteDirective='', seleniumFlag=False):
	
	print('\ngoogleGetHTMLPage() - start')
	if( len(searchString) == 0 ):
		return ''

	'''
	searchString = searchString.split(' ')
	queryFragment = ''
	for token in searchString:
		queryFragment = queryFragment + token + '+'
	queryFragment = queryFragment[:-1]
	'''

	searchQueryFragment = 'as_q=' + quote(searchString) + siteDirective
	if( page > 1 ):
		#to yield https://www.google.com/search?as_q=myQuery#q=myQuery&start=10 (for page 1)
		#anomaly - start
		#for reasons unknown, this block always got the first page
		#queryFragment = '#q=' + queryFragment
		#searchQueryFragment = searchQueryFragment + queryFragment + '&start=' + str((page-1) * 10)
		#anomaly - end

		searchQueryFragment = searchQueryFragment + '&start=' + str((page-1) * 10)

	searchQuery = 'https://www.google.com/search?' + searchQueryFragment
	print('\tsearchQuery:', searchQuery)
	
	#MOD
	#print(' CAUTION, COERCED RETURN ' * 4)
	#return ''

	googleHTMLPage = ''
	try:
		if( seleniumFlag ):
			from selenium import webdriver
			driver = webdriver.Firefox()
			waitSeconds = randint(2, 5)
			googleHTMLPage = seleniumLoadWebpage(driver, searchQuery, waitTimeInSeconds=waitSeconds, closeBrowerFlag=True)
		else:
			googleHTMLPage = dereferenceURI(searchQuery)
	except:
		googleHTMLPage = ''
		genericErrorInfo()

	print('\ngoogleGetHTMLPage() - end\n')
	return googleHTMLPage

#scraper
def googleRetrieveLinksFromPage(googleHTMLSoup, rankAdditiveFactor=0, page=1):

	if( len(googleHTMLSoup) ==  0 ):
		return {}

	#linksDict format: {link, [crawlDatetime|nowDatetime]}
	linksDict = {}
	rank = 0
	results = googleHTMLSoup.findAll('div', {'class': 'srg'})#'srg' or 'med'
	for result in results:

		liOrDiv = result.findAll('li', {'class': 'g'})
		if( len(liOrDiv) == 0 ):
			liOrDiv = result.findAll('div', {'class': 'g'})

		for resultInstance in liOrDiv:

			crawlDateTime = resultInstance.find('span', {'class':'f'})
			snippet = resultInstance.find('span', {'class':'st'})

			if( snippet is None ):
				snippet = ''
			else:
				snippet = snippet.text
				snippet = snippet.replace('<em>', '')
				snippet = snippet.replace('</em>', '')

			if( crawlDateTime is None ):
				crawlDateTime = str(datetime.now()).split('.')[0].replace(' ', 'T')
			else:
				#"Jul 25, 2015 -" or "Jul 2, 2015 -"
				try:
					crawlDateTime = crawlDateTime.text.strip().replace(' -', '')
					monthDayYear = crawlDateTime.split(', ')
					monthDay = monthDayYear[0].split(' ')
					year = monthDayYear[1].split()

					month = monthDay[0]
					day = monthDay[1]
					if( len(day) == 1 ):
						day = '0' + day
					year = year[0]

					crawlDateTime = datetime.strptime(month + ',' + day + ',' + year, '%b,%d,%Y')
					crawlDateTime = str(crawlDateTime).replace(' ', 'T')
				except:
					#if crawlDateTime does not meet expected format
					print('googleRetrieveLinksFromPage(): unexpected datetime format:', crawlDateTime)
					crawlDateTime = str(datetime.now()).split('.')[0].replace(' ', 'T')
			
			#print(crawlDateTime)

			title = resultInstance.h3.a.text
			#title = title.encode('ascii', 'ignore')

			titleLink = resultInstance.h3.a['href']
			titleLink = titleLink.strip()

			'''
			linksDict format:
			{
				'link': {'title': '', 'crawl-datetime': '', 'snippet': ''}
				...
			}
			'''
			#when signature changes change getListOfDict()
			rank += 1
			linksDict[titleLink] = {'title': title, 'crawl-datetime': crawlDateTime, 'snippet': snippet, 'rank': rank+rankAdditiveFactor, 'page': page}
			

	return linksDict

def googleGetSERPResultsList(query, maxPageToVisit=1, siteDirective='', pathFilenameMinusExtension=''):
	
	mergedListOfLinks = []
	pagePageLinksDict = googleGetSERPResults(query=query, maxPageToVisit=maxPageToVisit, siteDirective=siteDirective, pathFilenameMinusExtension=pathFilenameMinusExtension)
	sortedPages = sorted( pagePageLinksDict )

	for page in sortedPages:
		mergedListOfLinks += pagePageLinksDict[page]

	'''

		if( len(sortedPages) == 1 ):
			return pagePageLinksDict[0]
		else:
			for i in range(1, len(sortedPages)):
				page = sortedPages[i]
				prevPageLastRank = pagePageLinksDict[ page - 1 ]['rank']
	'''

	return mergedListOfLinks

def googleGetSERPResults(query, maxPageToVisit=1, siteDirective='', pathFilenameMinusExtension=''):
	print('\ngoogleGetSERPResults() - start')

	if( maxPageToVisit < 1 ):
		return {}

	'''
		pagePageLinksList format:
		{ 
			page:
			[ 
				(link: crawlDatetime or nowDatetime),
				(link: crawlDatetime or nowDatetime),
				...
			],
			page:
			[
			]
			,...
		}
	'''
	pagePageLinksDict = {}
	prevLinksDictKeys = []
	rankAdditiveFactor = 0
	for page in range(1, maxPageToVisit+1):
		print()
		print('\tpage:', page)
		
		#MOD
		googleHTMLPage = googleGetHTMLPage(query, page, siteDirective=siteDirective)
		if( len(googleHTMLPage) == 0 ):
			print('\tEmpty html page:', page, 'skipping')
			continue

		pathFilenameMinusExtension = pathFilenameMinusExtension.strip()
		if( len(pathFilenameMinusExtension) != 0 ):
			try:
				outfile = open(pathFilenameMinusExtension + '_Page_' + str(page) + '.html', 'w')
				outfile.write(googleHTMLPage)
				outfile.close()
			except:
				genericErrorInfo()

		soup = BeautifulSoup( googleHTMLPage, 'html.parser')
		'''
			linksDict format:
			{
				'link': {'title': '', 'crawlDatetime': '', 'snippet': ''}
				...
			}
		'''
		linksDict = googleRetrieveLinksFromPage( soup, rankAdditiveFactor=rankAdditiveFactor, page=page )

		#print('links:')
		#for link, datetimeVal in linksDict.items():
		#	print(link, datetimeVal)

		if( prevLinksDictKeys == linksDict.keys() ):
			print('\tDuplicate page:', page, 'stopping')
			break


		prevLinksDictKeys = linksDict.keys()
		pagePageLinksDict[page-1] = getListOfDict(linksDict)
		if( len(pagePageLinksDict[page-1]) != 0 ):
			rankAdditiveFactor = pagePageLinksDict[page-1][-1]['rank']

	'''
	pagePageLinksDict format:
	{ page, {link: crawlDatetime or nowDatetime} }
	'''
	print('googleGetSERPResults() - end\n')
	return pagePageLinksDict

def getListOfDict(linksDict):

	'''
		linksDict format:
		{
			'link': {'title': '', 'crawl-datetime': ''}
			...
		}
	'''
	sortedLinks = sorted( linksDict, key=lambda link:linksDict[link]['rank'] )
	listOfLinksDicts = []
	
	for link in sortedLinks:

		tempDict = {'link': link.strip()}
		for key, value in linksDict[link].items():
			
			if( isinstance(key, str) ):
				key = key.strip()

			if( isinstance(value, str) ):
				value = value.strip()
			
			tempDict[key] = value
		listOfLinksDicts.append(tempDict)

	return listOfLinksDicts

#google - end

def getLinks(uri='', html='', commaDelDomainsToExclude='', fromMainTextFlag=True):

	'''
	uri = uri.strip()
	if( len(uri) == 0 ):
		return []
	'''

	uri = uri.strip()
	if( len(uri) != 0 ):
		if( uri[-1] != '/' ):
			uri = uri + '/'

	domainsToExcludeDict = {}
	for domain in commaDelDomainsToExclude.split(','):
		domain = domain.strip()
		domainsToExcludeDict[domain] = True

	allLinks = []
	dedupDict = {}
	try:
		if( len(html) == 0 ):
			html = dereferenceURI(uri)
		
		if( fromMainTextFlag ):
			extractor = Extractor(extractor='ArticleExtractor', html=html)
			html = extractor.getHTML()

		soup = BeautifulSoup(html, 'html.parser' )
		links = soup.findAll('a')

		for i in range(0, len(links)):
			if( links[i].has_attr('href') ):

				link = links[i]['href'].strip()
				if( len(link) > 1 ):
					
					if( link[:2] == '//' ):
						link = 'http:' + link
					elif( link[0] == '/' ):
						link = uri + link[1:]
					
					if( link[:4] != 'http' ):
						continue

					if( getDomain(link) in domainsToExcludeDict ):
						continue
					
					if( link not in dedupDict ):
						allLinks.append(link)		
						dedupDict[link] = True
	except:
		genericErrorInfo()

	return allLinks

def dereferenceURI(URI, maxSleepInSeconds=5):
	
	#print('dereferenceURI():', URI)
	URI = URI.strip()
	if( len(URI) == 0 ):
		return ''
	
	htmlPage = ''
	try:
		'''
		if( debugModeFlag ):
			print('\toffline: reading from output.html')
			infile = open('output.html', 'r')
			htmlPage = infile.read()
			infile.close()
		'''
		
		if( maxSleepInSeconds > 0 ):
			randSleep(maxSleepInSeconds)

		htmlPage = mimicBrowser(URI)
	except:
		genericErrorInfo()
	
	return htmlPage

def getDomain(url):

	url = url.strip()
	if( len(url) == 0 ):
		return ''

	if( url.find('http') == -1  ):
		url = 'http://' + url

	domain = ''
	
	try:
		domain = urlparse(url)
	except:
		genericErrorInfo()
		return ''

	domain = domain.netloc.strip()

	indexOfDot = domain.find('www.')
	#remove www. prefix
	if( indexOfDot == 0 ):
		domain = domain[indexOfDot+4:]

	return domain

#http://stackoverflow.com/questions/4770297/python-convert-utc-datetime-string-to-local-datetime
# From 2015-07-12 18:45:11
def datetime_from_utc_to_local(utc_datetime):
	now_timestamp = time.time()
	offset = datetime.fromtimestamp(now_timestamp) - datetime.utcfromtimestamp(now_timestamp)
	return utc_datetime + offset

#directive: verify seleniums header
def getCustomHeaderDict():

	headers = {
		'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10.11; rv:38.0) Gecko/20100101 Firefox/38.0',
		'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
		'Accept-Language': 'en-US,en;q=0.5',
		'Accept-Encoding': 'gzip, deflate',
		'Connnection': 'keep-alive',
		'Cache-Control':'max-age=0'	
		}

	headers['User-Agent'] = 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/53.0.2785.143 Safari/537.36'

	return headers

def makeCurlHeadRequest(uri):

	output = check_output(['curl', '-s', '-I', '-L', uri])
	output = output.decode('utf-8')
	return output

def makeHeadRequest(uri):
	return mimicBrowser(uri, getRequestFlag=False)

def mimicBrowser(uri, getRequestFlag=True):
	
	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''

	try:
		headers = getCustomHeaderDict()
		response = ''

		if( getRequestFlag ):
			response = requests.get(uri, headers=headers, timeout=10)
			return response.text
		else:
			response = requests.head(uri, headers=headers, timeout=10)
			return response.headers
	except:

		genericErrorInfo()
		print('\tquery is: ', uri)
	
	return ''

def genericErrorInfo():
	exc_type, exc_obj, exc_tb = sys.exc_info()
	fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
	errorMessage = fname + ', ' + str(exc_tb.tb_lineno)  + ', ' + str(sys.exc_info())
	print('\tERROR:', errorMessage)
	
	outfile = open(workingFolder() + 'genericErrorDump.txt', 'w')
	outfile.write(getNowFilename() + '\n')
	outfile.write(errorMessage)
	outfile.close()
	

#precondition: dateA/dateB format - Fri, 04 Dec 1998 14:31:39 GMT (%a, %d %b %Y %H:%M:%S GMT)
def isDateBAfterDateA(dateA, dateB, convertToDateTimeObjFlag=False):

	try:
		if( convertToDateTimeObjFlag ):
			dateA = datetime.strptime(dateA, '%a, %d %b %Y %H:%M:%S GMT')
			dateB = datetime.strptime(dateB, '%a, %d %b %Y %H:%M:%S GMT')
	except:
		genericErrorInfo()
		return False

	if( dateB > dateA ):
		return True

	return False

def getUriDepth(uri):

	uri = uri.strip()
	if( len(uri) == 0 ):
		return -1

	if( uri[-1] == '/' ):
		uri = uri[:-1]

	try:
		components = urlparse(uri)
		return len(components.path.split('/')) - 1
	except:
		genericErrorInfo()
		return -1

def extractPageTitleFromHTML(html):

	title = ''
	try:
		soup = BeautifulSoup(html, 'html.parser')
		title = soup.find('title')

		if( title is None ):
			title = ''
		else:
			title = title.text.strip()
	except:
		genericErrorInfo()

	return title

def getPageTitle(uri, html=''):

	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''

	title = ''
	try:
		if( len(html) == 0 ):
			html = dereferenceURI(uri)

		title = extractPageTitleFromHTML(html)
	except:
		genericErrorInfo()
	

	return title.strip()


def removeEmptyLines(string):
	string = string.strip().replace('\n', ' ')
	return os.linesep.join([s for s in string.splitlines() if s])

def phantomJSTakeScreenshot(uri, resX, resY, outfilename):	
	
	from subprocess import call
	phantomscript = os.path.join( workingFolder() + 'webshots.js' )

	try:
		call(['phantomjs', phantomscript, uri, resX, resY, outfilename])
	except:
		genericErrorInfo()

def phantomJSGetHTML(uri):

	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''

	html = ''
	phantomscript = os.path.join( workingFolder() + 'phantomGetHTML.js' )

	try:
		output = check_output(['phantomjs', phantomscript, uri])
		output = output.decode('utf-8')
		return output
	except:
		genericErrorInfo()

	return html



def seleniumLoadPageScrollToEnd(driver, uri, waitTimeInSeconds=10, closeBrowerFlag=True, maxScroll=20):
	print('seleniumLoadWebpage():')

	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''
	html = ''
	#directive: consider phantom js but set header

	#driver = webdriver.PhantomJS()
	try:
		#driver = webdriver.Firefox()
		print('\tgetting:', uri)
		driver.get(uri)
		driver.maximize_window()

		prevLength = len(driver.page_source)
		print('\tprevLength:', prevLength)
		print('\tscrolling')
		driver.execute_script('window.scrollTo(0, document.body.scrollHeight);')

		randSleep()
		scrollCount = 0
		while( len(driver.page_source) > prevLength and scrollCount != maxScroll ):
			scrollCount += 1
			prevLength = len(driver.page_source)
			print('\tprevLength:', prevLength)
			print('\tscrolling')
			driver.execute_script('window.scrollTo(0, document.body.scrollHeight);')
			randSleep()


		html = driver.page_source.encode('utf-8')
		
		if( closeBrowerFlag ):
			driver.quit()
	except:
		genericErrorInfo()
		return ''

	return html

def seleniumLoadWebpage(driver, uri, waitTimeInSeconds=10, closeBrowerFlag=True):
	print('seleniumLoadWebpage():')

	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''
	html = ''

	#directive: consider phantom js but set header

	#driver = webdriver.PhantomJS()
	try:
		#driver = webdriver.Firefox()
		print('\tgetting:', uri)
		#driver.set_page_load_timeout(timeoutInSeconds)
		#driver.set_script_timeout(timeoutInSeconds)

		driver.get(uri)
		driver.maximize_window()

		if( waitTimeInSeconds > 0 ):
			print('\tsleeping in seconds:', waitTimeInSeconds)
			time.sleep(waitTimeInSeconds)

		html = driver.page_source.encode('utf-8')
		
		if( closeBrowerFlag ):
			driver.quit()
	except:
		genericErrorInfo()
		return ''

	return html

def seleniumSaveScreenshot(driver, uri, outfilename, waitTimeInSeconds=10):
	#make outfilename blank to close browser

	print('seleniumLoadWebpage():')

	uri = uri.strip()
	if( len(uri) == 0 ):
		return False

	outfilename = outfilename.strip()
	if( len(outfilename) == 0 ):
		print('\tclosing browser')
		driver.quit()
		return True

	
	#directive: consider phantom js but set header
	#driver = webdriver.PhantomJS()
	try:
		#driver = webdriver.Firefox()
		print('\tgetting:', uri)
		driver.get(uri)
		driver.maximize_window()

		print('\tsleeping in seconds:', waitTimeInSeconds)
		time.sleep(waitTimeInSeconds)

		driver.save_screenshot(outfilename)
		print('\tsaved screenshot:', outfilename)

		return True
	except:
		genericErrorInfo()

	return False

def getURIHash(uri):

	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''

	hash_object = hashlib.md5(uri.encode())
	return hash_object.hexdigest()

def isArchived(uri, mememtoAggregator='http://memgator.cs.odu.edu/'):

	print('\n\tisArchived():')
	print('\t\turi:', uri)
	uri = uri.strip()
	mememtoAggregator = mememtoAggregator.strip()

	if( len(uri) == 0 or len(mememtoAggregator) == 0 ):
		print('\tBad request uri or mememtoAggregator')
		return False

	#all mementos are archived
	if( len(getURIRFromMemento(uri)) != 0 ):
		print('\t\turi-r extracted from memento link:', uri)
		return True

	if( getMementoCount(uri, mememtoAggregator) > 0 ):
		return True
	else:
		return False

	'''
		#directive: get mementoAggregator from config
		output = ''
		try:
			output = check_output(['curl', '-I', '--silent', '-m', '20', mememtoAggregator + 'timemap/json/' + uri])
			output = output.decode('utf-8')
			output = output.lower()
		except:
			genericErrorInfo()
			print('\tquery is: ', uri)
			return False

		if( output.find('200 ok') != -1 ):
			return True

		return False
	'''

def getURIRFromMemento(memento):
	
	memento = memento.strip()
	if( len(memento) == 0 ):
		return ''

	indexOfLastScheme = memento.rfind('http')
	if( indexOfLastScheme < 1 ):
		return ''
	else:
		return memento[indexOfLastScheme:]

def getMementoCount(uri, mememtoAggregator='http://memgator.cs.odu.edu/', timeout='20'):

	print('\n\tgetMementoCount():')
	print('\t\turi:', uri)
	#print('\tmememtoAggregator:', mememtoAggregator)
	#print('\ttimeout', timeout)

	uri = uri.strip()
	mememtoAggregator = mememtoAggregator.strip()

	if( len(uri) == 0 or len(mememtoAggregator) == 0 ):
		print('\t\tBad request uri or mememtoAggregator')
		return -1

	#directive: get mementoAggregator from config
	output = ''
	mementoCount = 0
	try:
		output = check_output(['curl', '-I', '--silent', '-m', str(timeout), mememtoAggregator + 'timemap/json/' + uri])
		output = output.decode('utf-8')
		output = output.lower()
	except:
		genericErrorInfo()
		print('\t\tquery is: ', uri)
		return -1

	if( output.find('200 ok') != -1 ):
		mementoCountSign = 'x-memento-count:'
		beginIndex = output.find(mementoCountSign)
		
		if( beginIndex > -1 ):
			endIndex = output.find('\n', beginIndex + len(mementoCountSign))
			if( endIndex > beginIndex ):

				try:
					mementoCount = int(output[beginIndex + len(mementoCountSign):endIndex].strip())
				except:
					genericErrorInfo()

	return mementoCount

def expanUrlSecondTry(url):

	'''
	Attempt to get first good location. For defunct urls with previous past
	'''

	url = url.strip()
	if( len(url) == 0 ):
		return ''

	print('expanUrlSecondTry(): url - ', url)

	try:

		# when using find, use outputLowercase
		# when indexing, use output
		
		output = check_output(['curl', '-s', '-I', '-m', '10', url])
		output = output.decode('utf-8')
		
		outputLowercase = output.lower()
		indexOfLocation = outputLowercase.rfind('\nlocation:')

		if( indexOfLocation != -1 ):
			# indexOfLocation + 1: skip initial newline preceding location:
			indexOfNewLineAfterLocation = outputLowercase.find('\n', indexOfLocation + 1)
			redirectUrl = output[indexOfLocation:indexOfNewLineAfterLocation]
			redirectUrl = redirectUrl.split(' ')[1]

			return expanUrlSecondTry(redirectUrl)
		else:
			return url

	except:
		print('\terror url:', url)
		genericErrorInfo()
	

	return url

def expandUrl(url):

	'''
	Part A: Attempts to unshorten the uri until the last response returns a 200 or 
	Part B: returns the lasts good url if the last response is not a 200.
	'''
	url = url.strip()
	if( len(url) == 0 ):
		return ''
	
	try:
		#Part A: Attempts to unshorten the uri until the last response returns a 200 or 
		output = check_output(['curl', '-s', '-I', '-L', '-m', '10', '-c', 'cookie.txt', url])
		output = str(output)
		output = output.splitlines()
		
		longUrl = ''
		path = ''
		locations = []

		for line in output:
			line = line.strip()
			if( len(line) == 0 ):
				continue

			indexOfLocation = line.lower().find('location:')
			if( indexOfLocation != -1 ):
				#location: is 9
				locations.append(line[indexOfLocation + 9:].strip())

		if( len(locations) != 0 ):
			#traverse location in reverse: account for redirects to path
			#locations example: ['http://www.arsenal.com']
			#locations example: ['http://www.arsenal.com', '/home#splash']
			for url in locations[::-1]:
				
				if( url.strip().lower().find('/') == 0 and len(path) == 0 ):
					#find path
					path = url

				if( url.strip().lower().find('http') == 0 and len(longUrl) == 0 ):
					#find url
					
					#ensure url doesn't end with / - start
					if( url[-1] == '/' ):
						url = url[:-1]
					#ensure url doesn't end with / - end

					#ensure path begins with / - start
					if( len(path) != 0 ):
						if( path[0] != '/' ):
							path = '/' + path
					#ensure path begins with / - end

					longUrl = url + path

					#break since we are looking for the last long unshortened uri with/without a path redirect
					break
		else:
			longUrl = url




		return longUrl
	except:
		#Part B: returns the lasts good url if the last response is not a 200.
		print('\terror url:', url)
		genericErrorInfo()

		print('\tsecond try')
		return expanUrlSecondTry(url)


def expandUrl_obsolete1(url):

	url = url.strip()
	if( len(url) == 0 ):
		return ''

	try:
		# when using find, use outputLowercase
		# when indexing, use output
		
		output = check_output(['curl', '-s', '-I', '-L', '-m', '10', url])
		output = output.decode('utf-8')
		
		outputLowercase = output.lower()
		indexOfLocation = outputLowercase.rfind('\nlocation:')

		if( indexOfLocation != -1 ):
			# indexOfLocation + 1: skip initial newline preceding location:
			indexOfNewLineAfterLocation = outputLowercase.find('\n', indexOfLocation + 1)
			redirectUrl = output[indexOfLocation:indexOfNewLineAfterLocation]
			redirectUrl = redirectUrl.split(' ')[1]

			return redirectUrl
		else:
			return url
	except:
		print('\terror url:', url)
		genericErrorInfo()
		return url

def jaccardOverlapSim(str0, str1):
	return (jaccardFor2Words(str0, str1) + overlapFor2Words(str0, str1))/float(2)

def weightedJaccardOverlapSim(firstSet, secondSet, jaccardWeight=1, overlapWeight=1):

	denom = jaccardWeight + overlapWeight
	if( denom == 0 ):
		jaccardWeight = 1
		overlapWeight = 1

	return ((jaccardWeight * jaccardFor2Sets(firstSet, secondSet)) + (overlapWeight * overlapFor2Sets(firstSet, secondSet))) / denom

def jaccardFor2Sets(firstSet, secondSet):

	intersection = float(len(firstSet & secondSet))
	union = len(firstSet | secondSet)

	if( union != 0 ):
		return  round(intersection/union, 4)
	else:
		return 0

def overlapFor2Sets(firstSet, secondSet):

	intersection = float(len(firstSet & secondSet))
	minimum = min(len(firstSet), len(secondSet))

	if( minimum != 0 ):
		return  round(intersection/minimum, 4)
	else:
		return 0

def jaccardFor2Words(str0, str1):
	
	firstSet = set()
	secondSet = set()

	for token in str0:
		firstSet.add(token)

	for token in str1:
		secondSet.add(token)

	return jaccardFor2Sets(firstSet, secondSet)

def overlapFor2Words(str0, str1):

	firstSet = set()
	secondSet = set()

	for token in str0:
		firstSet.add(token)

	for token in str1:
		secondSet.add(token)

	return overlapFor2Sets(firstSet, secondSet)

def getConfigParameters(configPathFilename, keyValue=''):

	keyValue = keyValue.strip()
	configPathFilename = configPathFilename.strip()
	if( len(configPathFilename) == 0 ):
		return ''

	returnValue = ''

	try:
		configFile = open(configPathFilename, 'r')
		config = configFile.read()
		configFile.close()

		jsonFile = json.loads(config)

		if( len(keyValue) == 0 ):
			returnValue = jsonFile
		else:
			returnValue = jsonFile[keyValue]
	except:
		genericErrorInfo()

	return returnValue
#directive: googleRetrieveLinksFromPage() consider not relying on tag signature for retrieving links with site directive
#directive: mememetoAggregator single initialization and retrieval from a config file