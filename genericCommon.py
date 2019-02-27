#Python3

import re
import time
import json
import hashlib
import requests
import operator
import gzip
import os, sys, getopt

from bs4 import BeautifulSoup
from datetime import datetime

from subprocess import Popen
from multiprocessing import Pool
from subprocess import check_output

from functools import reduce
from random import randint
from os.path import dirname, abspath
from textstat.textstat import textstat
from urllib.parse import urlparse, quote, quote_plus
from tldextract import extract

from selenium.webdriver.common.keys import Keys
from selenium.webdriver.common.action_chains import ActionChains
from selenium.common.exceptions import TimeoutException

from boilerpipe.extract import Extractor
from newspaper import Article
from mimetypes import MimeTypes
from dateparser import parse as parseDateStr

#class DocVect - start
import math
import string
import numpy as np
from numpy import linalg as LA


from sklearn.metrics import pairwise_distances

from sklearn.feature_extraction.text import CountVectorizer
from sklearn.feature_extraction.text import TfidfTransformer
#class DocVect - start

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

def getTopKDomainStats(uris, k):

	domainDict = {}
	linkCount = len(uris)

	for uri in uris:
		domain = getDomain( uri )
		domainDict.setdefault(domain, 0)
		domainDict[domain] += 1


	if( len(domainDict) == 0 or k == 0 or linkCount == 0 ):
		return {}

	sortedTopKDomains = sorted( domainDict.items(), key=lambda x: x[1], reverse=True )
	sortedTopKDomains = sortedTopKDomains[:k]

	topKDomLinkCount = 0
	for i in range(len(sortedTopKDomains)):
		domain, domainCount = sortedTopKDomains[i]
		topKDomLinkCount += domainCount

	return {
		'link-count-aka-col-count': linkCount,
		'top-' + str(k) + '-domain-link-count': topKDomLinkCount,
		'frac-of-col': topKDomLinkCount/linkCount,
		'top-' + str(k) + '-domains': sortedTopKDomains
	}

def getURIEstCreationDate(uri, html='', verbose=True, cdPort='7777'):

	if( verbose ):
		print('getURIEstCreationDate():')

	if( len(html) == 0 ):
		html = dereferenceURI(uri, 0)

	creationDate = ''

	if( len(html) == 0 ):
		if( verbose ):
			print('\tuseCarbonDate():', uri)

		creationDate = useCarbonDate( uri, excludeBacklinks=True, excludeArchives=False, port=cdPort )
		creationDate = creationDate.replace('T', ' ')
	else:
		if( uri.startswith('https://twitter.com') ):
			
			if( verbose ):
				print('\tgetTweetPubDate():', uri)
			
			creationDate = getTweetPubDate(uri, html)
		elif( getUriDepth(uri) != 0 ):#not a homepage
			if( verbose ):
				print('\tgetArticlePubDate():', uri)

			creationDate = getArticlePubDate(uri=uri, html=html)

	if( len(creationDate) == 0 ):
		if( verbose ):
			print('\tlast try useCarbonDate():', uri)

		creationDate = useCarbonDate( uri, excludeBacklinks=True, excludeArchives=False, port=cdPort )
		creationDate = creationDate.replace('T', ' ')
	
	return creationDate

def getHostname(url, includeSubdomain=True):

	url = url.strip()
	if( len(url) == 0 ):
		return ''

	if( url.find('http') == -1  ):
		url = 'http://' + url

	domain = ''
	
	try:
		ext = extract(url)
		
		domain = ext.domain.strip()
		subdomain = ext.subdomain.strip()
		suffix = ext.suffix.strip()
		
		if( len(suffix) != 0 ):
			suffix = '.' + suffix 

		if( len(domain) != 0 ):
			domain = domain + suffix

		if( len(subdomain) != 0 ):
			subdomain = subdomain + '.'

		if( includeSubdomain ):
			domain = subdomain + domain
	except:
		genericErrorInfo()
		return ''

	return domain

def wsdlDiversityIndex(uriLst):
	diversityPerPolicy = {'uri-diversity': set(), 'hostname-diversity': set(), 'domain-diversity': set()}
	
	if( len(uriLst) == 0 ):
		return {}

	if( len(uriLst) == 1 ):
		for policy in diversityPerPolicy:
			diversityPerPolicy[policy] = 0
		return diversityPerPolicy

	for uri in uriLst:

		uriCanon = getDedupKeyForURI(uri)
		if( len(uriCanon) != 0 ):
			#get unique uris
			diversityPerPolicy['uri-diversity'].add( uriCanon )						
		
		hostname = getHostname(uri)
		if( len(hostname) != 0 ):
			#get unique hostname
			diversityPerPolicy['hostname-diversity'].add( hostname )					

		domain = getHostname(uri, includeSubdomain=False)
		if( len(domain) != 0 ):
			#get unique domain	
			diversityPerPolicy['domain-diversity'].add( domain )
	
	for policy in diversityPerPolicy:
		U = len(diversityPerPolicy[policy])
		N = len(uriLst)
		diversityPerPolicy[policy] = (U - 1)/(N - 1)

	return diversityPerPolicy

#modified: https://github.com/oduwsdl/archivenow/blob/master/archivenow/handlers/ia_handler.py
def archiveNowProxy(uri, params=None):
	
	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''

	if( params is None ):
		params = {}

	if( 'timeout' not in params ):
		params['timeout'] = 10

	try:
		uri = 'https://web.archive.org/save/' + uri
		headers = getCustomHeaderDict()
		
		# push into the archive
		r = requests.get(uri, timeout=params['timeout'], headers=headers, allow_redirects=True)
		r.raise_for_status()
		# extract the link to the archived copy 
		if (r == None):
			print('\narchiveNowProxy(): Error: No HTTP Location/Content-Location header is returned in the response')
			return ''
			
		if 'Location' in r.headers:
			return r.headers['Location']
		elif 'Content-Location' in r.headers:
			return 'https://web.archive.org' + r.headers['Content-Location']	
		else:
			for r2 in r.history:
				if 'Location' in r2.headers:
					return r2.headers['Location']
				if 'Content-Location' in r2.headers:
					return r2.headers['Content-Location']
	except Exception as e:
		print('Error: ' + str(e))
	except:
		genericErrorInfo()
	
	return ''

def sendToWebArchive(url):

	url = url.strip()
	if( len(url) == 0 ):
		return False

	goodResponseFlagArchive0 = True
	headers = getCustomHeaderDict()

	try:
		response = requests.get('http://web.archive.org/save/' + url, headers=headers, timeout=10)
		print( response.headers )
	except:
		goodResponseFlagArchive0 = False
		genericErrorInfo()


	return goodResponseFlagArchive0

def sendToArchiveIs(url):

	url = url.strip()
	if( len(url) == 0 ):
		return False

	goodResponseFlagArchive1 = True
	headers = getCustomHeaderDict()
	try:
		r = requests.post('https://archive.is/submit/', headers=headers, data={'url': url})
		if( r.status_code > 300 ):
			goodResponseFlagArchive1 = False

	except:
		goodResponseFlagArchive1 = False
		genericErrorInfo()

	return goodResponseFlagArchive1

def isURISocialMedia(uri):

	uri = uri.strip()
	if( len(uri) == 0 ):
		return False

	socialMediaDoms = set(
		[
			'twitter.com', 
			'facebook.com', 
			'youtube.com',
			'instagram.com',
			'tumblr.com'
		])

	if( getDomain(uri) in socialMediaDoms ):
		return True
	else:
		return False


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

def getFolderSize(folder):
	
	try:
		return check_output(['du','-sh', folder]).split()[0].decode('utf-8')
	except:
		genericErrorInfo()
		return ''

def workingFolder():
	return dirname(abspath(__file__)) + '/'

def createFolderAtPath(path):

	if( os.path.exists(path) == False ):
		try:
			check_output(['mkdir', path])
			#print('\tcreateFolderAtPath(): created new folder for col:', path)
		except:
			genericErrorInfo()
			print('\tcreateFolderAtPath() error creating', path)

def getNowFilename():
	filename = str(datetime.now()).split('.')[0]
	return filename.replace(' ', 'T').replace(':', '-')

def getNowTime():

	now = str(datetime.now()).split('.')[0]
	return now

#dict - start

def sortDctByKey(dct, key, reverse=True):

	key = key.strip()
	if( len(dct) == 0 or len(key) == 0 ):
		return []

	return sorted(dct.items(), key=lambda x: x[1][key], reverse=reverse)

def getFromDict(dataDict, mapList):
	#credit: https://stackoverflow.com/a/14692747
	
	try:
		return reduce(operator.getitem, mapList, dataDict)
	except Exception as e:
		if( isinstance(e, KeyError) == False ):
			genericErrorInfo()
		return None

def setInDict(dataDict, mapList, value):
	#credit: https://stackoverflow.com/a/14692747
	try:
		getFromDict(dataDict, mapList[:-1])[mapList[-1]] = value
	except:
		genericErrorInfo()

def getDictFromFile(filename):

	try:

		if( os.path.exists(filename) == False ):
			return {}

		return getDictFromJson( readTextFromFile(filename) )
	except:
		print('\tgetDictFromFile(): error filename', filename)
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
		'done': True,
		'should': True,
		'would': True,
		'now': True, #from sklearn stopwords
		'also': True, 
		'find': True, 
		'besides': True, 
		'neither': True, 
		'moreover': True, 
		'elsewhere': True, 
		'seemed': True, 
		'amoungst': True, 
		'cannot': True, 
		'whereupon': True, 
		'since': True, 
		'perhaps': True, 
		'rather': True, 
		'must': True, 
		'thereafter': True, 
		'whither': True, 
		'often': True, 
		'enough': True, 
		'whose': True, 
		'toward': True, 
		'put': True, 
		'else': True, 
		'others': True, 
		'sometime': True, 
		'go': True, 
		'everywhere': True,
		'onto': True, 
		'yet': True, 
		'although': True, 
		'anything': True, 
		'though': True,
		'several': True, 
		're': True, 
		'amongst': True, 
		'least': True,
		'whatever': True, 
		'thus': True,
		'across': True, 
		'beforehand': True, 
		'anyone': True,
		'whenever': True, 
		'ie': True, 
		'hereupon': True, 
		'nobody': True, 
		'beyond': True, 
		'someone': True, 
		'along': True, 
		'take': True, 
		'therefore': True, 
		'however': True, 
		'another': True, 
		'whether': True, 
		'anyhow': True, 
		'within': True, 
		'anyway': True, 
		'etc': True,
		'etc.': True, 
		'nothing': True, 
		'somehow': True, 
		'thereby': True, 
		'therein': True, 
		'either': True, 
		'eg': True, 
		'e.g': True,
		'e.g.': True,
		'towards': True,
		'via': True,
		'thru': True, 
		'already': True, 
		'keep': True, 
		'upon': True, 
		'us': True,
		'less': True, 
		'back': True, 
		'wherein': True, 
		'afterwards': True, 
		'whence': True, 
		'without': True, 
		'hereby': True, 
		'whoever': True, 
		'sometimes': True, 
		'become': True, 
		'nevertheless': True, 
		'amount': True, 
		'every': True, 
		'around': True, 
		'formerly': True, 
		'inc': True, 
		'inc.': True,
		'hereafter': True, 
		'nowhere': True, 
		'among': True, 
		'un': True, 
		'co': True, 
		'see': True, 
		'whereafter': True, 
		'mine': True, 
		'anywhere': True, 
		'much': True, 
		'next': True, 
		'whole': True, 
		'none': True, 
		'latter': True, 
		'everything': True, 
		'can\'t': True,
		'cant': True, 
		'behind': True, 
		'could': True, 
		'somewhere': True, 
		'whereas': True, 
		'ever': True, 
		'couldn\'t': True,
		'couldnt': True, 
		'beside': True, 
		'still': True, 
		'may': True, 
		'seem': True, 
		'even': True, 
		'many': True, 
		'wherever': True, 
		'except': True, 
		'alone': True, 
		'indeed': True, 
		'describe': True, 
		'thence': True, 
		'everyone': True, 
		'thin': True, 
		'seems': True,
		'almost': True, 
		'throughout': True, 
		'side': True, 
		'together': True, 
		'became': True, 
		'always': True, 
		'herein': True, 
		'mostly': True, 
		'otherwise': True, 
		'namely': True, 
		'thereupon': True, 
		'get': True, 
		'meanwhile': True, 
		'hasnt': True,
		'hasn\'t'
		'hence': True, 
		'whereby': True, 
		'never': True, 
		'something': True
	}
	
	return stopwordsDict
#dict - end


#html - start

#twitter.nodejs - start
def nodeExtractTweetsFromSearch(query='', uri='', maxTweetCount=100, latestVerticalFlag=False):

	query = query.strip()
	uri = uri.strip()

	if( len(query) == 0 and len(uri) == 0 ):
		return {}

	if( latestVerticalFlag ):
		latestVerticalFlag = 'f=tweets&'
	else:
		latestVerticalFlag = ''

	twitterURIPrefix = 'https://twitter.com/search?' + latestVerticalFlag + 'q='#top
	finalTweetsColDict = {}

	if( len(query) != 0 ):
		searchURI = twitterURIPrefix + quote_plus( query ) + '&src=typd'

		try:
			output = check_output([workingFolder() + 'nodejs-client/twt-client.js', str(maxTweetCount), searchURI])
			output = output.decode('utf-8')
			output = output.split('JSON-OUTPUT:')[1]
			finalTweetsColDict = getDictFromJson(output)
		except:
			genericErrorInfo()

	else:
		for urlPrefix in ['url:', '']:
			searchURI = twitterURIPrefix + quote_plus( urlPrefix + uri ) + '&src=typd'

			try:
				output = check_output([workingFolder() + 'nodejs-client/twt-client.js', str(maxTweetCount), searchURI])
				output = output.decode('utf-8')
				output = output.split('JSON-OUTPUT:')[1]
				finalTweetsColDict = getDictFromJson(output)
			except:
				genericErrorInfo()

			if( len(finalTweetsColDict) != 0 ):
				break

	return finalTweetsColDict

def nodeExtractTweetsFromTweetURI(tweetConvURI, maxTweetCount=100):

	tweetConvURI = tweetConvURI.strip()
	if( tweetConvURI.find('https://twitter.com/') != 0 ):
		return {}

	if( maxTweetCount < 1 ):
		maxTweetCount = 100


	finalTweetsColDict = {}
	try:
		output = check_output([workingFolder() + 'nodejs-client/twt-client.js', str(maxTweetCount), tweetConvURI])
		output = output.decode('utf-8')
		output = output.split('JSON-OUTPUT:')[1]
		finalTweetsColDict = getDictFromJson(output)
	except:
		genericErrorInfo()


	return finalTweetsColDict

def nodeExtractVideoLinkFromTweet(tweetURI):
	
	try:
		twitterHTMLPage = nodeLoadWebpage(tweetURI, throttleSeconds=2)
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
#twitter.nodejs - end

def extractFavIconFromHTML(html, sourceURL):
	sourceURL = sourceURL.strip()
	favicon = ''
	try:
		soup = BeautifulSoup(html, 'html.parser')
		links = soup.findAll('link')
		breakFlag = False
		for link in links:
			if( link.has_attr('rel') ):
				for rel in link['rel']:
					
					rel = rel.lower().strip()
					if( rel.find('icon') != -1 or rel.find('shortcut') != -1 ):
						favicon = link['href'].strip()
						breakFlag = True
						break

			if( breakFlag ):
				break

		if( len(favicon) != 0 and len(sourceURL) != 0 ):
			if( favicon.find('//') == 0 ):
				favicon = 'http:' + favicon
			elif( favicon[0] == '/' ):
				scheme, netloc, path, params, query, fragment = urlparse( sourceURL )
				favicon = scheme + '://' + netloc + favicon
	except:
		genericErrorInfo()

	return favicon

def clean_html(html, method='python-boilerpipe'):
	
	if( len(html) == 0 ):
		return ''

	#experience problem of parallelizing, maybe due to: https://stackoverflow.com/questions/8804830/python-multiprocessing-pickling-error
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

def getArticlePubDate(uri, html):

	if( len(html) == 0 ):
		return ''

	try:
		article = Article(uri)
		article.download(input_html=html)
		article.parse()

		if( article.publish_date is None ):
			return ''
		else:
			pubdate = article.publish_date
			return str(pubdate.date()) + ' ' + str(pubdate.time())
	except:
		genericErrorInfo()

	return ''

#html - end


#text - start

def sanitizeText(text):

	#UnicodeEncodeError: 'utf-8' codec can't encode character '\ud83d' in position 3507: surrogates not allowed
	try:
		text.encode('utf-8')
	except UnicodeEncodeError as e:
		if e.reason == 'surrogates not allowed':	
			text = text.encode('utf-8', 'backslashreplace').decode('utf-8')
	except:
		text = ''

	return text

def getHashForText(text):
	hash_object = hashlib.md5( text.encode() )
	return hash_object.hexdigest()

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
		if char not in string.punctuation:
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

def nlpIsServerOn(host='localhost'):

	try:
		response = requests.head('http://' + host +':9000/')
		
		if( response.status_code == 200 ):
			return True
		else:
			return False

	except:
		genericErrorInfo()

	return False

def nlpServerStartStop(msg='start'):

	if( msg == 'start' ):
		try:
			if( nlpIsServerOn() ):
				print('\tCoreNLP Server already on - no-op')
			else:
				print('\tStarting CoreNLP Server')
				#docker run --rm -d -p 9000:9000 --name stanfordcorenlp anwala/stanfordcorenlp
				check_output([
					'docker', 
					'run', 
					'--rm', 
					'-d', 
					'-p', 
					'9000:9000', 
					'--name',
					'stanfordcorenlp',
					'anwala/stanfordcorenlp'
				])

				#warm up server (preload libraries, so subsequent responses are quicker)
				nlpGetEntitiesFromText('A quick brown fox jumped over the lazy dog')
		except:
			genericErrorInfo()
	elif( msg == 'stop' ):
		try:
			check_output(['docker', 'rm', '-f', 'stanfordcorenlp'])
		except:
			genericErrorInfo()


def nlpStartServer_obsolete():
	
	try:

		proc = Popen(workingFolder() + 'corenlp/run.sh')
		
		#enable server to load modules
		time.sleep(2)
		text = 'The quick brown fox jumped over the lazy dog.'
		Popen(['wget', '-q', '-O', '-', '--post-data', text, 'localhost:9000/?properties={"annotators":"entitymentions","outputFormat":"json","date":"2017-11-04T19:03:47"}'])
	except:
		genericErrorInfo()

def nlpStopServer_obsolete():

	try:
		check_output(['docker', 'rm', '-f', 'corenlpCon'])
	except:
		genericErrorInfo()


#iso8601Date: YYYY-MM-DDTHH:MM:SS
def nlpGetEntitiesFromText(text, host='localhost', iso8601Date='', labelLst=['PERSON','LOCATION','ORGANIZATION','DATE','MONEY','PERCENT','TIME'], params=None):

	if( params is None ):
		params = {}

	iso8601Date = iso8601Date.strip()

	#set default params - start
	if( 'normalizedTimeNER' not in params ):
		params['normalizedTimeNER'] = False
	#set default params - start

	'''
	if( params['normalizedTimeNER'] ):
		if( iso8601Date == '' ):
			iso8601Date = getNowTime().replace(' ', 'T')
	else:
		iso8601Date = ''
	'''

	labelLst = set(labelLst)
	if( len(iso8601Date) != 0 ):
		iso8601Date = ',"date":"' + iso8601Date + '"'

	request = host + ':9000/?properties={"annotators":"entitymentions","outputFormat":"json"' + iso8601Date + '}'
	entities = []
	dedupSet = set()

	try:
		output = check_output(['wget', '-q', '-O', '-', '--post-data', text, request])
		parsed = json.loads(output.decode('utf-8'))
		#dumpJsonToFile( 'output.json', parsed )

		if( 'sentences' not in parsed ):
			return []

		for sent in parsed['sentences']:
			
			if( 'entitymentions' not in sent ):
				continue

			for entity in sent['entitymentions']:

				#text is entity, ner is entity class
				dedupKey = entity['text'] + entity['ner']
				
				if( dedupKey in dedupSet or entity['ner'] not in labelLst ):
					continue
					
				#debug - start
				if( entity['ner'] == 'DATE' or entity['ner'] == 'TIME' ):
					if( params['normalizedTimeNER'] and 'normalizedNER' in entity ):
						#attempt to parse date
						parsedDate = genericParseDate( entity['normalizedNER'][:10] )
						if( parsedDate is not None ):
							entity['text'] = parsedDate.isoformat()[:19]
						else:
							entity['text'] = ''
				#debug - end

				if( len(entity['text']) != 0 ):
					entities.append( [entity['text'], entity['ner']] )
					dedupSet.add(dedupKey)
	except:
		genericErrorInfo()

	return entities

#iso8601Date: YYYY-MM-DDTHH:MM:SS
def nlpGetDatesFromText(text, iso8601Date=''):

	iso8601Date = iso8601Date.strip()
	if( len(iso8601Date) != 0 ):
		iso8601Date = ',"date":"' + iso8601Date + '"'

	request = 'localhost:9000/?properties={"annotators":"entitymentions","outputFormat":"json"' + iso8601Date + '}'
	datestimes = []
	dedupSet = set()

	try:
		output = check_output(['wget', '-q', '-O', '-', '--post-data', text, request])
		parsed = json.loads(output.decode('utf-8'))

		if( 'sentences' not in parsed ):
			return []

		for sent in parsed['sentences']:
			
			if( 'entitymentions' not in sent ):
				continue

			for entity in sent['entitymentions']:
				
				if( 'TIME' != entity['ner'] and entity['ner']  != 'DATE' ):
					continue

				dedupKey = entity['text'] + entity['ner']
				
				if( dedupKey not in dedupSet ):
					if( 'normalizedNER' in entity ):

						time = entity['normalizedNER'].split('T')[0].strip()
						
						try:
							datetime.strptime( time, '%Y-%m-%d' )
							datestimes.append( time + ' 00:00:00' )
						except:
							pass

						dedupSet.add(dedupKey)
	except:
		genericErrorInfo()

	return datestimes


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

def getDictFromJsonGZ(path):

	json = getTextFromGZ(path)
	if( len(json) == 0 ):
		return {}
	return getDictFromJson(json)

def getTextFromGZ(path):
	
	try:
		infile = gzip.open(path, 'rb')
		txt = infile.read().decode('utf-8')
		infile.close()

		return txt
	except:
		genericErrorInfo()

	return ''

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
		print('\treadTextFromFile()error filename:', infilename)
		genericErrorInfo()

	return text

def dumpJsonToFile(outfilename, dictToWrite, indentFlag=True, extraParams=None):

	if( extraParams is None ):
		extraParams = {}

	if( 'verbose' not in extraParams ):
		extraParams['verbose'] = True

	try:
		outfile = open(outfilename, 'w')
		
		if( indentFlag ):
			json.dump(dictToWrite, outfile, ensure_ascii=False, indent=4)#by default, ensure_ascii=True, and this will cause  all non-ASCII characters in the output are escaped with \uXXXX sequences, and the result is a str instance consisting of ASCII characters only. Since in python 3 all strings are unicode by default, forcing ascii is unecessary
		else:
			json.dump(dictToWrite, outfile, ensure_ascii=False)

		outfile.close()

		if( extraParams['verbose'] ):
			print('\twriteTextToFile(), wrote:', outfilename)
	except:
		if( extraParams['verbose'] ):
			print('\terror: outfilename:', outfilename)
		genericErrorInfo()
#file - end

#twitter - start

def isIsolatedTweet(twtDct):
	
	try:
		#first condition is for root tweet
		if( twtDct['data-conversation-id'] == twtDct['data-tweet-id'] and twtDct['tweet-stats']['reply'] == 0 ):
			return True
		else:
			return False
	except:
		genericErrorInfo()

	return None

#extract 863007411132649473 from 'https://twitter.com/realDonaldTrump/status/863007411132649473'
def getTweetIDFromStatusURI(tweetURI):

	if( tweetURI.startswith('https://twitter.com/') == False ):
		return ''

	tweetURI = tweetURI.strip()

	if( tweetURI[-1] == '/' ):
		tweetURI = tweetURI[:-1]

	if( tweetURI.find('status/') != -1 ):
		return tweetURI.split('status/')[1].strip()

	return ''

def parseTweetURI(tweetURI):

	twtDat = {'screenName': '', 'id': ''}
	if( tweetURI.startswith('https://twitter.com/') == False ):
		return twtDat


	tweetURI = tweetURI.strip()
	parts = urlparse(tweetURI)
	tweetURI = parts.scheme + '://' + parts.netloc + parts.path

	if( tweetURI[-1] == '/' ):
		tweetURI = tweetURI[:-1]

	if( tweetURI.find('status/') != -1 ):
		twtDat['id'] = tweetURI.split('status/')[1].strip()
		twtDat['id'] = twtDat['id'].split('?')[0].strip()
		twtDat['screenName'] = tweetURI.split('https://twitter.com/')[1].replace('/status/' + twtDat['id'], '')

	return twtDat

def getTweetLink(screenName, tweetId):
	return 'https://twitter.com/' + screenName + '/status/' + tweetId

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

	

def extractTweetsFromSearch(query='', uri='', maxTweetCount=100, chromedriverPath='/usr/bin/chromedriver', latestVerticalFlag=False, extraParams=None):

	query = query.strip()
	uri = uri.strip()

	if( len(query) == 0 and len(uri) == 0 ):
		return {}

	if( extraParams is None ):
		extraParams = {}

	if( latestVerticalFlag ):
		latestVerticalFlag = 'f=tweets&'
	else:
		latestVerticalFlag = ''

	twitterURIPrefix = 'https://twitter.com/search?' + latestVerticalFlag + 'q='#top

	if( 'maxNoMoreTweetCounter' not in extraParams ):
		extraParams['maxNoMoreTweetCounter'] = 2

	finalTweetsColDict = {}
	if( len(query) != 0 ):
		searchURI = twitterURIPrefix + quote_plus( query ) + '&src=typd'
		finalTweetsColDict = extractTweetsFromTweetURI(
			searchURI, 
			maxTweetCount, 
			maxNoMoreTweetCounter=extraParams['maxNoMoreTweetCounter'],
			chromedriverPath=chromedriverPath,
			extraParams=extraParams
		)
	else:
		for urlPrefix in ['url:', '']:
			searchURI = twitterURIPrefix + quote_plus( urlPrefix + uri ) + '&src=typd'
			finalTweetsColDict = extractTweetsFromTweetURI(
				searchURI, 
				maxTweetCount, 
				maxNoMoreTweetCounter=extraParams['maxNoMoreTweetCounter'],
				chromedriverPath=chromedriverPath,
				extraParams=extraParams
			)

			if( len(finalTweetsColDict) != 0 ):
				break
	
	return finalTweetsColDict

#maxRetryCount: -1 means unlimited
def retryParallelTwtsExt(urisLst, maxRetryCount=10, tweetConvMaxTweetCount=100, maxNoMoreTweetCounter=2, chromedriverPath='/usr/bin/chromedriver', extraParams=None):

	
	if( extraParams is None ):
		extraParams = {}

	result = []
	errorReqsDict = {}
	counter = 0
	extraParams['reportError'] = True


	while counter < maxRetryCount:

		tmpResult = parallelGetTwtsFrmURIs(
			urisLst,
			tweetConvMaxTweetCount=tweetConvMaxTweetCount,
			maxNoMoreTweetCounter=maxNoMoreTweetCounter,
			chromedriverPath=chromedriverPath,
			extraParams=extraParams
		)
		
		urisLst = []
		for res in tmpResult:
			if( 'error' in res ):
				urisLst.append( res['self'] )
				
				#save problematic request result payload, in case loop doesn't get chance to run again
				errorReqsDict[res['self']] = res
			else:
				result.append( res )

				if( res['self'] in errorReqsDict ):
					#remove this rectified request
					del errorReqsDict[res['self']]

		print('\nretryParallelTwtsExt, iter:', counter, 'of', maxRetryCount, ', queue:', len(urisLst))
		if( len(urisLst) == 0 ):
			print('\n\tbreaking, queue empty')
			break
		
		counter += 1

	for uri, res in errorReqsDict.items():
		result.append(res)

	return result

def parallelGetTwtsFrmURIs(urisLst, tweetConvMaxTweetCount=100, maxNoMoreTweetCounter=2, chromedriverPath='/usr/bin/chromedriver', extraParams=None):
	print('\nparallelGetTwts')

	if( len(urisLst) == 0 ):
		return []

	if( extraParams is None ):
		extraParams = {}

	offset = 0
	if( 'windowShiftOffset' in extraParams ):
		offset = extraParams['windowShiftOffset']
		print('\toffset:', offset)

	jobsLst = []
	predefXYLocs = [
		(0 + offset, 0),
		(200 + offset, 0),
		(400 + offset, 0),
		(600 + offset, 0),
		(0 + offset, 380),
		(200 + offset, 380),
		(400 + offset, 380),
		(600 + offset, 380)
	]

	indxer = 0
	length = len(urisLst)
	for i in range(length):
		
		locExtraParams = {}
		locExtraParams['windowX'], locExtraParams['windowY'] = predefXYLocs[indxer]
		indxer += 1
		indxer = indxer % len(predefXYLocs)

		#transfer props
		for key, val in extraParams.items():
			locExtraParams[key] = val

		keywords = {
			'tweetConvURI': urisLst[i],
			'tweetConvMaxTweetCount': tweetConvMaxTweetCount,
			'maxNoMoreTweetCounter': maxNoMoreTweetCounter,
			'chromedriverPath': chromedriverPath,
			'extraParams': locExtraParams
		}

		printMsg = '\t' + str(i) + ' of ' + str(length)
		jobsLst.append( {'func': extractTweetsFromTweetURI, 'args': keywords, 'misc': False, 'print': printMsg} )


	outLst = []
	resLst = parallelTask(jobsLst, threadCount=4)
	
	for res in resLst:
		res['output']['stats'] = {'total-links': 0, 'total-tweets': 0}
		if( len(res['output']) != 0 and 'tweets' in res['output'] ):
			res['output']['stats']['total-links'] = countLinksInTweets( res['output']['tweets'] )
			res['output']['stats']['total-tweets'] = len(res['output']['tweets'])
		
		outLst.append( res['output'] )

	return outLst

def countLinksInTweets(tweets):
	
	totalLinks = 0
	for twt in tweets:
		totalLinks += len(twt['tweet-links'])

	return totalLinks

def readTwtCache(cacheFolder, tweetURI):
	
	twtDat = parseTweetURI(tweetURI)
	cacheFolder = cacheFolder.strip()

	if( len(cacheFolder) != 0 and len(twtDat['screenName']) != 0 and len(twtDat['id']) != 0 ):
		return getDictFromFile(cacheFolder + twtDat['screenName'] + '-' + twtDat['id'] + '.json')

	return {}

def writeTwtCache(cacheFolder, tweetURI, twtDct):

	cacheFolder = cacheFolder.strip()
	if( len(cacheFolder) == 0 or len(twtDct) == 0 ):
		return

	twtDat = parseTweetURI(tweetURI)
	if( len(twtDat['screenName']) == 0 or len(twtDat['id']) == 0 ):
		return

	twtFileName = cacheFolder + twtDat['screenName'] + '-' + twtDat['id'] + '.json'
	dumpJsonToFile(twtFileName, twtDct, indentFlag=False)
	

def extractTweetsFromTweetURI(tweetConvURI, tweetConvMaxTweetCount=100, maxNoMoreTweetCounter=2, chromedriverPath='/usr/bin/chromedriver', extraParams=None):
	#patched use of Chrome with:https://archive.is/94Idt
	#set noMoreTweetCounter to -1 if no scroll required
	from selenium import webdriver

	tweetConvURI = tweetConvURI.strip()
	finalTweetsColDict = {}
	cacheMiss = False
	if( tweetConvURI.find('https://twitter.com') != 0 ):
		return {}

	if( extraParams is None ):
		extraParams = {}

	print('\nextractTweetsFromTweetURI():')
	print('\turi:', tweetConvURI)

	if( 'cache' in extraParams ):
		print('\tCACHE ON')
		print('\t', extraParams['cache'])
	else:
		print('\tCACHE OFF')
		extraParams['cache'] = {
			'folder': '',
			'read': False,
			'write': False
		}


	#check if tweet in cache - start
	if( len(extraParams['cache']['folder']) != 0  and extraParams['cache']['read'] ):
		print('\tcache read')
		finalTweetsColDict = readTwtCache(extraParams['cache']['folder'], tweetConvURI)

	if( extraParams['cache']['read'] and len(finalTweetsColDict) == 0 ):
		print('\tcache MISS')
	
	elif( len(finalTweetsColDict) != 0 ):
		print('\tcache HIT')
		return finalTweetsColDict
	#check if tweet in cache - end

	closeBrowerFlag = True
	reportErrorFlag = False
	if( tweetConvMaxTweetCount < 1 ):
		tweetConvMaxTweetCount = 100

	if( 'windowWidth' not in extraParams ):
		extraParams['windowWidth'] = 840

	if( 'windowHeight' not in extraParams ):
		extraParams['windowHeight'] = 380

	if( 'closeBrowerFlag' in extraParams ):
		closeBrowerFlag = extraParams['closeBrowerFlag']

	if( 'reportError' in extraParams ):
		reportErrorFlag = extraParams['reportError']

	if( 'driver' in extraParams ):
		driver = extraParams['driver']
		print('\tusing user-supplied driver')
	else:
		driver = webdriver.Chrome(executable_path=chromedriverPath)
		driver.set_window_size(extraParams['windowWidth'], extraParams['windowHeight'])
		if( 'windowX' in extraParams and 'windowY' in extraParams ):
			driver.set_window_position(extraParams['windowX'], extraParams['windowY'] )


	try:
		#driver.maximize_window()
		driver.get(tweetConvURI)
	except:
		print('\tsupplied chromedriverpath:', chromedriverPath)
		print('\t\ttweetConvURI:', tweetConvURI)
		genericErrorInfo()
		if( reportErrorFlag ):
			return {
				'error': True,
				'self': tweetConvURI
			}	

		return {}


	finalTweetsColDict = recursiveExtractTweetsMain(
		driver=driver, 
		tweetConvURI=tweetConvURI, 
		tweetConvMaxTweetCount=tweetConvMaxTweetCount, 
		maxNoMoreTweetCounter=maxNoMoreTweetCounter,
		extraParams=extraParams
	)
	
	validFileFlag = False
	if( len(finalTweetsColDict) != 0 ):
		validFileFlag = True

	#anomaly: not closing browser only seems to work when the user supplies the driver
	if( closeBrowerFlag ):
		driver.quit()
	
	finalTweetsColDict['self'] = tweetConvURI

	#update cache - start
	if( len(extraParams['cache']['folder']) != 0  and extraParams['cache']['write'] and validFileFlag ):
		print('\tupdating cache')
		writeTwtCache(extraParams['cache']['folder'], tweetConvURI, finalTweetsColDict)
	#update cache - end
	return finalTweetsColDict

def twitterGetTweetFromMoment(uri='', twitterHTMLPage='', maxSleepInSeconds=0):

	if( len(twitterHTMLPage)==0 ):
		twitterHTMLPage = dereferenceURI(uri, maxSleepInSeconds)

	try:
		soup = BeautifulSoup(twitterHTMLPage, 'html.parser')
	except:
		genericErrorInfo()
		return {}

	moments = soup.findAll('div', {'class': 'MomentCapsuleItemTweet'})
	tweetsLst = {
		'self': uri,
		'payload': [],
		'category': '',
		'pub-datetime': '',
		'description': '',
		'timestamp': getNowTime()
	}

	commonAccessors = {
		'category': {'class': 'MomentCapsuleSubtitle-category', 'tag': 'span'},
		'pub-datetime': {'class': 'MomentCapsuleSubtitle-context', 'tag': 'span'},
		'description': {'class': 'MomentCapsuleCover-description', 'tag': 'div'}
	}

	for common, dets in commonAccessors.items():
		relAbsTime = soup.find(dets['tag'], {'class': dets['class']})
		if( relAbsTime is not None ):
			tweetsLst[common] = relAbsTime.text.strip()

	for moment in moments:
		tweet = twitterGetTweetIfExist(moment)
		if( len(tweet) != 0 ):
			tweetsLst['payload'].append(tweet)
	
	return tweetsLst

def prepTwtsForRetrn(finalTweetsColDict, tweets):
	for key, val in tweets.items():
		finalTweetsColDict[key] = val

def recursiveExtractTweetsMain(driver, tweetConvURI, finalTweetsColDict=None, tweetConvMaxTweetCount=100, maxNoMoreTweetCounter=2, extraParams=None):

	#set maxNoMoreTweetCounter to -1 if you don't want any scroll
	print('\nrecursiveExtractTweetsMain()')
	print('\turi:', tweetConvURI)

	tweetConvURI = tweetConvURI.strip()
	if( len(tweetConvURI) == 0 ):
		return {}

	if( extraParams is None ):
		extraParams = {}

	if( 'maxNoMoreTweetCounter' not in extraParams ):
		extraParams['maxNoMoreTweetCounter'] = maxNoMoreTweetCounter

	if( 'dedupSet' not in extraParams ):
		extraParams['dedupSet'] = set()

	if( tweetConvMaxTweetCount < 1 ):
		tweetConvMaxTweetCount = 100

	if( finalTweetsColDict is None ):
		finalTweetsColDict = {}
		finalTweetsColDict['is-thread'] = False
		finalTweetsColDict['tweets'] = []


	finalTweetsColDictPrevLen = len(finalTweetsColDict['tweets'])

	print('\ttweet count:', finalTweetsColDictPrevLen)
	print('\tmaxNoMoreTweetCounter:', maxNoMoreTweetCounter)
	print('\ttweetConvMaxTweetCount:', tweetConvMaxTweetCount)
	

	try:
		clickShowMore(driver)
		twitterHTMLPage = driver.page_source.encode('utf-8')
		tweets = twitterGetDescendants(twitterHTMLPage, uri=tweetConvURI)

		for twt in tweets['tweets']:
			if( twt['data-tweet-id'] in extraParams['dedupSet'] ):
				continue
			
			extraParams['dedupSet'].add( twt['data-tweet-id'] )
			finalTweetsColDict['tweets'].append( twt )

		if( len(tweets['tweets']) > tweetConvMaxTweetCount ):
			print('\tinput limit reached:', tweetConvMaxTweetCount)
			
			#get proper count of tweets, since tweets sets retrieved in different sessions may have identical pos values
			prepTwtsForRetrn(finalTweetsColDict, tweets)
			finalTweetsColDict['tweets'] = finalTweetsColDict['tweets'][:tweetConvMaxTweetCount]
			return finalTweetsColDict

		if( finalTweetsColDictPrevLen == len(finalTweetsColDict['tweets']) ):
			maxNoMoreTweetCounter -= 1
		else:
			print('\tresetting maxNoMoreTweetCounter to:', maxNoMoreTweetCounter)
			maxNoMoreTweetCounter = extraParams['maxNoMoreTweetCounter']

		if( maxNoMoreTweetCounter < 1 ):
			print('\tno more tweets, breaking after tweets count:', len(finalTweetsColDict['tweets']))
			
			#get proper count of tweets, since tweets sets retrieved in different sessions may have identical pos values
			prepTwtsForRetrn(finalTweetsColDict, tweets)
			return finalTweetsColDict

		scrollDown(driver, tweetConvURI)
		recursiveExtractTweetsMain(driver, tweetConvURI, finalTweetsColDict, tweetConvMaxTweetCount, maxNoMoreTweetCounter, extraParams)
	except:
		genericErrorInfo()

	return finalTweetsColDict
	
def clickShowMore(driver):

	script = '''
		//revise when better understanding of DOM is established
		var showMoreSignature = ['ThreadedConversation-moreRepliesLink', 'ThreadedConversation-showMoreThreadsButton' ,'show-more-link', 'new-tweets-bar', 'Tombstone-action'];
		for(var i = 0; i<showMoreSignature.length; i++)
		{
			for( var j = 0; j<2; j++ )
			{

				var showMore;
				if( j == 0 )
				{
					showMore = document.querySelectorAll( '[class="' + showMoreSignature[i] + '"]' );
				}
				else
				{
					showMore = document.getElementsByClassName( showMoreSignature[i] );
				}

				for(var k=0; k<showMore.length; k++)
				{
					showMore[k].click();
				}

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

def scrollDown(driver, uri):
	
	if( uri.find('/status/') != -1 ):
		
		'''
		#obsolete: this function doesn't work in firefox and scrollIntoView() did not work
		maxScroll = 15
		sleepSeconds = 1
		actions = ActionChains(driver)
		for i in range(maxScroll):
			actions.send_keys(Keys.SPACE).perform()
			print('\tscrollDown():', i, 'of', maxScroll)
			time.sleep(sleepSeconds)
		'''

		script = '''
			var tweets = document.getElementsByClassName('tweet');
			if( tweets.length != 0 )
			{
				tweets[tweets.length-1].scrollIntoView();
			}
		'''

		script = '''
			var flexMods = document.getElementsByClassName('flex-module-inner');
			if( flexMods.length != 0 )
			{
				flexMods[flexMods.length-1].scrollIntoView();
			}
		'''
		driver.execute_script(script)
	else:
		driver.execute_script('window.scrollTo(0, document.body.scrollHeight);')

def twitterGetDescendants(twitterHTMLPage, uri='', extraParams=None):

	if( len(twitterHTMLPage) == 0 ):
		return {}
	
	if( extraParams is None ):
		extraParams = {}

	tweetsLst = []
	tweetCounter = 0
	rootTwt = {}
	isImplicitThreadPresent = False
	conversationMarker = False
	threadTypes = []
	

	soup = BeautifulSoup(twitterHTMLPage, 'html.parser')
	tweets = soup.find_all(class_='tweet')
	uriDets = twitterGetURIDetails(uri)

	#method 1 of identifying threads: check if this is a conversation thread - start
	if( soup.find(class_='ThreadedConversation--selfThread') is not None ):
		#this marker seems not usually present when thread is accessed from some children
		conversationMarker = True
		threadTypes.append('explicit')#CAUTION MOVING THIS STATMENT, POSITION SENSITIVE for threadTypes
	#method 1 of identifying threads: check if this is a conversation thread - end

	for i in range(len(tweets)):
		
		tweetHtml = tweets[i]
		tweets[i] = twitterGetTweetIfExist( tweets[i] )
		if( len(tweets[i]) != 0 ):

			tweets[i]['pos'] = tweetCounter		
			if( conversationMarker ):
				tweets[i]['extra']['in-explicit-thread'] = recursiveIsTwtInSelfChain( tweetHtml );
				#special case since head of thread is not part of self chain
				if( tweets[i]['data-conversation-id'] == tweets[i]['data-tweet-id'] ):
					tweets[i]['extra']['in-explicit-thread'] = True

			if( len(uriDets) == 2 ):
				if( tweets[i]['data-conversation-id'] == tweets[i]['data-tweet-id'] ):
					rootTwt = tweets[i]
					

			tweetsLst.append( tweets[i] )
			tweetCounter += 1

	#method 2 of identifying threads - start
	tweetsLst = sorted(tweetsLst, key=lambda k: k['pos'])
	if( len(uriDets) == 2 ):
		isImplicitThreadPresent = isTwtsThreadMarkImpThread(rootTwt, tweetsLst)
		if( isImplicitThreadPresent == True ):
			threadTypes.append('implicit')
	#method 2 of identifying threads - end
	
	if( len(threadTypes) == 2 ):
		#the presence of explicit thread overrides implicit
		threadTypes = 'explicit'
	elif( len(threadTypes) == 1 ):
		threadTypes = 'implicit'
	else:
		threadTypes = ''

	return { 
		'is-thread': isImplicitThreadPresent or conversationMarker,
		'thread-type': threadTypes,
		'tweets': tweetsLst
	}

def twitterGetURIDetails(uri):

	uriDets = {}
	uri = uri.split('/status/')

	if( len(uri) == 2 ):
	
		screenName = ''
		screenName = uri[0].split('https://twitter.com/')
		
		if( len(screenName) == 2 ):
			screenName = screenName[1]
		else:
			screenName = ''
		
		if( len(screenName) != 0 ):
			uriDets['screenName'] = screenName
			uriDets['id'] = uri[1]

	return uriDets

def isTwtsThreadMarkImpThread(rootTwt, tweetsLst):
	
	if( len(tweetsLst) < 2 ):
		return False

	threadFlag = False
	rootTweetPos = -1
	implicitThreads = []

	for i in range(len(tweetsLst)):
		
		tweetsLst[i]['extra']['in-implicit-thread'] = False
		if( tweetsLst[i]['data-conversation-id'] != rootTwt['data-conversation-id'] ):
			continue
			
		#The root tweet in a conversation: data-conversation-id = data-tweet-id
		if( tweetsLst[i]['data-tweet-id'] == rootTwt['data-conversation-id']  ):
			rootTweetPos = i
			#e.g., https://twitter.com/KevinMKruse/status/1025944636693651457
		elif( tweetsLst[i]['data-screen-name'] == rootTwt['data-screen-name']  ):
			#Here means a tweet that is not the root tweet has been found that replied the root tweet, from the same author

			skipFlag = True
			if( 'replying-to' in tweetsLst[i]['extra'] ):
				if( tweetsLst[i]['extra']['replying-to'][0] == rootTwt['data-screen-name'] ):
					
					if( len(tweetsLst[i]['extra']['replying-to']) == 1 ):
						tweetsLst[i]['extra']['in-implicit-thread'] = True
						skipFlag = False
						#e.g., https://twitter.com/dtdchange/status/1020855197642510336
					else:
						#immediate parent tweet has same author, but disjoint thread replying another tweet
						#e.g., https://twitter.com/KevinMKruse/status/1029832219727196160	
						tweetsLst[i]['extra']['nested-implicit-thread'] = True
			else:
				#immediate parent tweet has same author, not replying another tweet
				#e.g., https://twitter.com/KevinMKruse/status/1058093798935400448
				tweetsLst[i]['extra']['in-implicit-thread'] = True
				skipFlag = False

			if( skipFlag ):
				continue
			
			
			threadFlag = True
			tmp = {}
			tmp['id'] = tweetsLst[i]['data-tweet-id']
			tmp['pos'] = i#this pos is different from tweetsLst[i].pos since the latter accounts for tweets that are not members of the thread.
			implicitThreads.append( tmp )
			

	if( threadFlag == True and rootTweetPos != -1 ):
		tweetsLst[rootTweetPos]['extra']['in-implicit-thread'] = True
		tweetsLst[rootTweetPos]['extra']['reply-group'] = implicitThreads
	
	return threadFlag

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

def getTweetPubDate(tweetURI, tweetHtml):

	tweetID = getTweetIDFromStatusURI(tweetURI)
	if( len(tweetID) == 0 ):
		return ''

	tweetDate = ''
	tweetDict = twitterGetDescendants(tweetHtml, uri=tweetURI)
	
	if( tweetID in tweetDict ):
		try:
			tweetDate = tweetDict[tweetID]['tweet-time'].split(' - ')[-1].strip()
			tweetDate = str(datetime.strptime(tweetDate, '%d %b %Y'))
		except:
			genericErrorInfo()

	return tweetDate

def recursiveIsTwtInSelfChain(tweetDiv):

	parent = tweetDiv.parent
	classNames = []

	if( parent is None ):
		return False
	elif( parent.has_attr('class') ):
		classNames = parent['class']

	for i in range( len(classNames) ):	
		if( classNames[i].strip().lower() == 'threadedconversation--selfthread' ):
			return True
	
	return recursiveIsTwtInSelfChain(parent)

def twitterGetTweetIfExist(potentialTweetDiv):

	tweetDict = {};
	listOfTweetAttrs = ['data-tweet-id', 'data-name', 'data-screen-name']

	for attr in listOfTweetAttrs:
		if( potentialTweetDiv.has_attr(attr) ):
			tweetDict[attr] = potentialTweetDiv[attr]
		else:
			print('missing attr:', attr)

	if( len(tweetDict) != len(listOfTweetAttrs) ):
		return {}

	tweetDict['tweet-text'] = ''
	tweetDict['tweet-time'] = ''
	tweetDict['user-verified'] = False
	tweetDict['tweet-links'] = []
	tweetDict['tweet-stats'] = {}
	tweetDict['extra'] = {}
	tweetDict['hashtags'] = []
	tweetDict['is-video-adaptive-present'] = False
	uniformAccessAttrs = ['data-conversation-id', 'data-mentions']

	tweetTag = potentialTweetDiv.find_all(class_='tweet-text')
	if( len(tweetTag) != 0 ):
		tweetDict['tweet-text'] = tweetTag[0].text

	tweetTag = potentialTweetDiv.find_all(class_='tweet-timestamp')
	if( len(tweetTag) != 0 ):
		if( tweetTag[0].has_attr('title') ):
			tweetDict['tweet-time'] = tweetTag[0]['title']

	if( potentialTweetDiv.find(class_='Icon--verified') is not None ):
		tweetDict['user-verified'] = True

	for attr in uniformAccessAttrs:
		tweetDict[attr] = ''
		if( potentialTweetDiv.has_attr(attr) ):
			tweetDict[attr] = potentialTweetDiv[attr]

	tweetDict['tweet-links'] = twitterGetLinksFromTweetDiv(potentialTweetDiv)
	tweetDict['is-video-adaptive-present'] = isVideoAdaptiveMediaInTweet(potentialTweetDiv)

	#get stats - start
	uniformAccessAttrs = ['reply', 'retweet', 'favorite']
	for attr in uniformAccessAttrs:
		
		tweetDict['tweet-stats'][attr] = 0
		stat = potentialTweetDiv.find(class_='ProfileTweet-action--' + attr)
		
		if( stat is not None ):
			stat = stat.text.split(' ')[0].strip();
			if( stat.isdigit() ):
				tweetDict['tweet-stats'][attr] = int(stat)
	#get stats - end

	showThread = potentialTweetDiv.find(class_='show-thread-link')
	
	if( showThread is not None ):
		if( showThread.has_attr('href') == True ):
			
			link = showThread['href'].split('status/')
			if( len(link) == 2 and 'data-conversation-id' in tweetDict ):
				tweetDict['extra']['thread'] = 'https://twitter.com' + link[0] + 'status/' + tweetDict['data-conversation-id']
	
	#find "Replying to" - start
	replyingTo = potentialTweetDiv.find(class_='ReplyingToContextBelowAuthor')
	if( replyingTo is not None ):
		
		replyAcnts = replyingTo.findAll(class_='js-user-profile-link')
		for i in range(len(replyAcnts)):
			if( replyAcnts[i].has_attr('href') == True ):
				tweetDict['extra'].setdefault('replying-to', [])
				tweetDict['extra']['replying-to'].append( replyAcnts[i]['href'].replace('/', '') )

	#find "Replying to" - start

	#add hashtags - start
	hashtags = potentialTweetDiv.findAll(class_='twitter-hashtag')
	for i in range( len(hashtags) ):
		tweetDict['hashtags'].append( hashtags[i].text.strip() )
	#add hashtags - end

	#final formatting - start
	tweetDict['data-mentions'] = tweetDict['data-mentions'].strip()
	if( len(tweetDict['data-mentions']) == 0 ):
		tweetDict['data-mentions'] = []
	else:
		tweetDict['data-mentions'] = tweetDict['data-mentions'].split(' ')
	#final formatting - end		
		
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

def optIsURIInTweet(link, maxSleep=3):

	print('\noptIsURIInTweet()')

	urir = getURIRFromMemento(link)
	if( len(urir) != 0 ):
		print('\t\turi-r extracted from memento link, to be checked in tweet index')
		link = urir

	tweetPath = ''

	for urlPrefix in ['url:', '']:
		print('\t\turi prefix:', urlPrefix)
		uri = 'https://twitter.com/search?f=tweets&q=' + quote_plus(urlPrefix + link) + '&src=typd'
		htmlPage = dereferenceURI(uri, maxSleep)
		soup = BeautifulSoup( htmlPage, 'html.parser' )
		tweetPath = isTweetPresent(soup)

		if( len(tweetPath) != 0 ):
			break

	return tweetPath

def isURIInTweet(link, driver=None, closeBrowserFlag=True, chromedriverPath='/usr/bin/chromedriver'):

	print('\nisURIInTweet()')

	urir = getURIRFromMemento(link)
	if( len(urir) != 0 ):
		print('\t\turi-r extracted from memento link, to be checked in tweet index')
		link = urir

	tweetPath = ''
	if( driver is None ):
		from selenium import webdriver
		try:
			driver = webdriver.Chrome(executable_path=chromedriverPath)
		except:
			genericErrorInfo()
			return ''

	for urlPrefix in ['url:', '']:
		print('\t\turi prefix:', urlPrefix)
		uri = 'https://twitter.com/search?f=tweets&q=' + quote_plus(urlPrefix + link) + '&src=typd'
		htmlPage = seleniumLoadWebpage(driver, uri, waitTimeInSeconds=1, closeBrowerFlag=False)
		soup = BeautifulSoup( htmlPage, 'html.parser' )
		tweetPath = isTweetPresent(soup)

		if( len(tweetPath) != 0 ):
			break

	if( closeBrowserFlag == True ):
		driver.quit()

	return tweetPath
#twitter - end

#sutori - start
def sutoriGetExLinks(html):

	if( len(html) == 0 ):
		return []

	payload = []

	try:
		soup = BeautifulSoup(html, 'html.parser')
		mainPage = soup.find('', {'class': 'main'})

		if( mainPage is not None ):

			links = mainPage.find_all('a')
			for l in links:
				
				if( l.has_attr('href') == False ):
					continue

				l['href'] = l['href'].strip()
				if( len(l['href']) == 0 ):
					continue

				if( l['href'][0] == '/' ):
					continue

				if( l['href'].find('https://www.sutori.com/') == 0 ):
					continue

				payload.append( {'uri': l['href'], 'title': l.text.strip(), 'tag': 'a'} )

			
			possibleLinks = mainPage.find_all('p')
			for l in possibleLinks:
				l = l.text.strip()
				
				if( l.find('http') != 0 ):
					continue

				payload.append( {'uri': l, 'title': '', 'tag': 'p'} )

			imgs = mainPage.find_all('img')
			for img in imgs:
				
				if( img.has_attr('src') == False ):
					continue

				title = ''
				if( img.has_attr('alt') ):
					title = img['alt']

				payload.append( {'uri': img['src'], 'title': title, 'tag': 'img'} )
	except:
		genericErrorInfo()

	return payload

def sutoriStopHandler(html, params):
	
	print('\n\tsutoriStopHandler()')
	print('\tparams:', params)

	maxStories = 0
	if( 'maxStories' in params ):
		maxStories = params['maxStories']

	output = {}
	output['stop'] = False
	output['output'] = []

	try:
		soup = BeautifulSoup(html, 'html.parser')
		comStories = soup.findAll('', {'class': 'community-stories'})
		if( len(comStories) != 0 ):
			
			storyBoxes = comStories[0].findAll('div', {'class': 'story-box'})
			for storyBox in storyBoxes:
				link = storyBox.find('a', {'class': 'story-link'})
				
				if( link is None ):
					continue

				if( link.has_attr('href') == False ):
					continue

				link['href'] = link['href'].strip()
				if( len(link['href']) == 0 ):
					continue

				if( link['href'][0] == '/' ):
					link['href'] = 'https://www.sutori.com' + link['href']
				
				linkDict = {'story': link['href'], 'title': '', 'author': ''}
				author = storyBox.find('', {'class': 'story-author-name'})
				title = storyBox.find('', {'class': 'story-title'})

				if( author is not None ):
					linkDict['author'] = author.text.strip()

				if( title is not None ):
					linkDict['title'] = title.text.strip()

				linkDict['pos'] = len(output['output'])
				output['output'].append( linkDict )
				outputSize = len(output['output'])

				if( outputSize == maxStories ):
					output['stop'] = True
					break
	except:
		genericErrorInfo()

	return output

def sutoriSearch(query, chromedriverPath='/Users/renaissanceassembly/bin/chromedriver', maxStories=10):
	query = query.strip()
	if( len(query) == 0 ):
		return {}

	from selenium import webdriver
	uri = 'https://www.sutori.com/stories/search?query=' + query.replace(' ', '%20')
	payload = {'self': uri, 'timestamp': getNowTime()}
	stopHandlerParams = {'maxStories': maxStories}

	print('\nsutoriSearch():')
	print('\turi:', uri)

	driver = webdriver.Chrome(executable_path=chromedriverPath)
	driver.set_window_size(1000, 840)
	extraParams = {
		'stopHandler': sutoriStopHandler,
		'stopHandlerParams': stopHandlerParams
	}
	res = seleniumLoadPageScrollToEnd(driver, uri, extraParams=extraParams)
	driver.quit()
	print('\tres keys:', res.keys())
	
	payload['payload'] = []
	if( 'output' in res ):
		payload['payload'] = res['output']

	print('\tExtracting links')
	driver = webdriver.Chrome(executable_path=chromedriverPath)
	driver.set_window_size(1000, 1000)
	payloadCount = len(payload['payload'])
	
	for i in range(payloadCount):
		
		print('\t\t', i, 'of', payloadCount)
		uri = payload['payload'][i]['story']
	
		waitTimeInSeconds = 3
		extraParams = {'script': 'window.scrollTo(0, document.body.scrollHeight);'}
		html = seleniumLoadWebpage(driver, uri, closeBrowerFlag=False, waitTimeInSeconds=waitTimeInSeconds, extraParams=extraParams)
		payload['payload'][i]['links'] = sutoriGetExLinks(html)

	driver.quit()
	

	return payload
#sutori - end

#scoop.it - start
def scoopitExtractTopics(uri, html, container, page, topicMaxPages, extraParams=None):

	print('\nscoopitExtractTopics():')
	print('\turi:', uri)

	if( len(html) == 0 ):
		return False

	if( extraParams is None ):
		extraParams = {}

	try:
		soup = BeautifulSoup(html, 'html.parser')
		topics = soup.findAll('div', {'class': 'theme'})

		if('maxTopics' in extraParams):
			topics = topics[:extraParams['maxTopics']]

		if( len(topics) == 0 ):
			print('\tno more topics, returning')
			return True

		for i in range(len(topics)):
			
			print('\t\ttopic', i, 'of', len(topics))
			title = topics[i].find('div', {'class': 'theme-title'})
			if( title is None ):
				continue

			title = title.find('a')
			if( title is None ):
				continue
			
			linkDct = {}
			if( title.has_attr('href') == False ):
				continue

			linkDct['uri'] = title['href']
			linkDct['title'] = title.text.strip()
			linkDct['curated-by'] = {}
			linkDct['posts'] = []

			for j in range(1, topicMaxPages+1):
				print('\t\t\tpage', j, 'of', topicMaxPages)
				print('\t\t\turi:', linkDct['uri'])
				html = dereferenceURI(linkDct['uri'], 3)

				if( j == 1 ):
					linkDct['curated-by'] = scoopitGetTopicCurator(html)

				noMoreFlag = scoopitExtractPosts(linkDct['uri'], html, linkDct['posts'], j)
				if( noMoreFlag ):
					print('\t\t\tno more scoops for topic, breaking')
					print()
		
			container.append( linkDct )
	except:
		genericErrorInfo()

	return False

def scoopitGetTopicCurator(html):

	try:
		soup = BeautifulSoup(html, 'html.parser')
		soup = soup.find('div', {'id': 'themeAuthor'})
		
		if( soup is None ):
			return {}
			
		soup = soup.find('a')
		if( soup is None ):
			return {}

		author = {'uri': '', 'name': ''}
		author['name'] = soup.text.strip()
		if( soup.has_attr('href') ):
			
			author['uri'] = soup['href'].strip()
			if( len(author['uri']) != 0 ):
				if( author['uri'][0] == '/' ):
					author['uri'] = 'https://www.scoop.it' + author['uri']
		
		return author
	except:
		genericErrorInfo

	return {}


def scoopitExtractPosts(uri, html, container, page):

	if( len(html) == 0 ):
		return False
	
	searchFlag = True
	pageTitle = ''
	if( uri.find('https://www.scoop.it/search') == -1 ):
		searchFlag = False
		pageTitle = getPageTitle(uri=uri, html=html)

	try:
		soup = BeautifulSoup(html, 'html.parser')
		posts = soup.findAll('div', {'class': 'post'})

		if( len(posts) == 0 ):
			print('\tno more scoops, returning\n')
			return True

		for post in posts:
			
			link = post.find('h2', {'class': 'postTitleView'})
			postUser = post.find('table', {'class': 'posthistory'})
			postCreationDate = post.find('div', {'class': 'post-metas'})
			if( link is None ):
				continue

			link = link.find('a', {'rel': 'nofollow'})
			if( link is None ):
				continue

			linkDct = {}
			linkDct['title'] = link.text.strip()
			linkDct['uri'] = ''
			
			if( link.has_attr('href') == False ):
				continue
			
			linkDct['scooped-by'] = {}
			linkDct['scooped-onto'] = {}
			linkDct['creation-date'] = ''
			linkDct['uri'] = link['href']

			#get post creation date - start
			if( postCreationDate is not None ):
				
				postCreationDate = postCreationDate.find_all('a')
				if( len(postCreationDate) != 0 ):
					
					postCreationDate = postCreationDate[-1]
					if( postCreationDate.has_attr('href') ):
						linkDct['creation-date'] = postCreationDate.text.strip()
			#get post creation date - end

			if( postUser is not None ):
				postUser = postUser.findAll('a')
				if( len(postUser) > 1 ):
					
					if( searchFlag ):
						if( postUser[-2].has_attr('href') ):
							linkDct['scooped-by']['name'] = postUser[-2].text.strip()
							linkDct['scooped-by']['uri'] = postUser[-2]['href'].strip()

						if( postUser[-1].has_attr('href') ):
							linkDct['scooped-onto']['name'] = postUser[-1].text.strip()
							linkDct['scooped-onto']['uri'] = postUser[-1]['href'].strip()
					else:
						if( postUser[-1].has_attr('href') ):
							linkDct['scooped-by']['name'] = postUser[-1].text.strip()
							linkDct['scooped-by']['uri'] = postUser[-1]['href']

						linkDct['scooped-onto']['name'] = pageTitle
						linkDct['scooped-onto']['uri'] = uri

					for uriOpt in ['scooped-by', 'scooped-onto']:
						if( 'uri' in linkDct[uriOpt] ):
							if( len(linkDct[uriOpt]['uri']) != 0 ):
								if( linkDct[uriOpt]['uri'][0] == '/' ):
									linkDct[uriOpt]['uri'] = 'https://www.scoop.it' + linkDct['scooped-by']['uri']
					'''
					if( 'uri' in linkDct['scooped-onto'] ):
						if( len(linkDct['scooped-onto']['uri']) != 0 ):
							if( linkDct['scooped-onto']['uri'][0] == '/' ):
								linkDct['scooped-onto']['uri'] = 'https://www.scoop.it' + linkDct['scooped-onto']['uri']
					'''
			

			linkDct['page'] = page
			linkDct['rank'] = len(container) + 1
			container.append(linkDct)
	except:
		genericErrorInfo()

	return False

def scoopitSearch(query, SERPMaxPages=1, postVerticalFlag=True, topicMaxPages=1, extraParams=None):
	
	print('\nscoopitSearch():')
	query = query.strip()
	payload = {
		'self': '',
		'payload': [],
		'max-pages': SERPMaxPages
	}

	if( len(query) == 0 ):
		return payload

	if( extraParams is None ):
		extraParams = {}

	query = query.replace(' ', '+')
	if( SERPMaxPages < 1 ):
		SERPMaxPages = 1 

	vertical = ''
	if( postVerticalFlag ):
		vertical = 'post'
	else:
		vertical = 'topic'


	for i in range(1, SERPMaxPages+1):
		
		uri = 'https://www.scoop.it/search?q=' + query + '&type=' + vertical
		payload['self'] = uri
		uri = uri + '&page=' + str(i)
		
		print('\turi:', uri)
		html = dereferenceURI(uri)
		if( len(html) == 0 ):
			return payload
		
		noMoreFlag = False
		if( vertical == 'post' ):
			print('\textracting posts')
			noMoreFlag = scoopitExtractPosts(uri, html, payload['payload'], i)
		else:
			noMoreFlag = scoopitExtractTopics(uri, html, payload['payload'], i, topicMaxPages, extraParams=extraParams)

		if( noMoreFlag ):
			print('\tnoMoreFlag set, breaking')
			break

		print()

	payload['timestamp'] = getNowTime()
	payload['scoop-count'] = len(payload['payload'])
	return payload
#scoop.it - end


#reddit - start
def redditSearch(query, subreddit='', maxPages='', extraFieldsDict=None, extraParams=None):

	print('\nredditSearch() - start')

	query = query.strip()
	subreddit = subreddit.strip()
	maxPages = str(maxPages).strip()
	sortFlag = ''
	randSleep = 0

	if( len(maxPages) == 0 ):
		maxPages = 0

	if( extraFieldsDict is None ):
		extraFieldsDict = {}

	if( extraParams is None ):
		extraParams = {}

	try:
		maxPages = int(maxPages)
	except:
		genericErrorInfo()
		maxPages = 0


	if( len(query) == 0 ):
		return {}

	if( len(subreddit) != 0 ):
		subreddit = 'r/' + subreddit + '/'


	if( 'sort' in extraParams ):
		extraParams['sort'] = extraParams['sort'].strip()
		if( len(extraParams['sort']) != 0 ):
			#default is: relevance, 
			#other options: top, new, comments
			sortFlag = '&sort=' + extraParams['sort']
			print('\tsort:', extraParams['sort'])

	if( 'maxSleep' in extraParams ):
		randSleep = extraParams['maxSleep']

	if( 'maxResults' not in extraParams ):
		extraParams['maxResults'] = -1

	print('\tquery:', query)
	print('\tsubreddit:', subreddit)
	afterFlag = ''
	collection = {
		'payload': [], 
		'stats': {'serp-link-dist': {}}
	}
	breakFlag = False

	try:
		while True:
			print()
			redditQuery = 'https://www.reddit.com/' + subreddit +  'search.json?q=' + quote(query) + sortFlag + afterFlag
			collection['self'] = redditQuery
			redditJson = getDictFromJson( dereferenceURI(redditQuery, randSleep) )
			collection['timestamp'] = getNowTime().replace('T', ' ')

			print('\tredditQuery:', redditQuery)

			if( 'data' not in redditJson ):
				print('\tNo data key present')
				break

			redditJson = redditJson['data']

			for child in redditJson['children']:
				
				try:

					tempDict = redditSetCommonDets( child['data'] )
					tempDict['kind'] = ''
					if( 'kind' in child ):
						tempDict['kind'] = redditKindTraslate(child['kind'])

					tempDict['links'] = redditGetAllLinksFromCommentHTML( child['data']['selftext_html'] )
					for key, value in extraFieldsDict.items():
						tempDict[key] = value

					linkDistCount = len(tempDict['links'])
					collection['stats']['serp-link-dist'].setdefault(linkDistCount, 0)
					collection['stats']['serp-link-dist'][linkDistCount] += 1

					collection['payload'].append(tempDict)

					if( len(collection['payload']) == extraParams['maxResults'] ):
						breakFlag = True
						print('\tmax results breaking:', extraParams['maxResults'])
						break

					'''
						print('\t\tauthor:', child['author'])
						print('\t\ttitle:', child['title'])
						print('\t\tsubreddit:', child['subreddit'])
						print()
					'''
				except:
					genericErrorInfo()
			
			maxPages -= 1
			print('\tmaxPages:', maxPages)

			if( breakFlag ):
				break
			
			if( maxPages > 0 and redditJson['after'] ):
				afterFlag = '&after=' + redditJson['after']
			else:
				break
	except:
		genericErrorInfo()

	print('redditExpand() - end\n')
	
	return collection


def redditSearchExpand(query, subreddit='', maxPages='', extraFieldsDict=None, extraParams=None):
	print('\nredditSearchExpand()')

	if( extraFieldsDict is None ):
		extraFieldsDict = {}

	if( extraParams is None ):
		extraParams = {}
	
	results = redditSearch(
		query=query,
		subreddit=subreddit,
		maxPages=maxPages,
		extraFieldsDict=extraFieldsDict,
		extraParams=extraParams
	)

	if( 'payload' not in results ):
		return results

	if( 'maxComments' not in extraParams ):
		extraParams['maxComments'] = -1

	if( 'maxSleep' not in extraParams ):
		extraParams['maxSleep'] = 2

	jobsLst = []
	size = len(results['payload'])
	for i in range(size):
		
		if( results['payload'][i]['stats']['comment-count'] == 0 ):
			continue

		keywords = {
			'commentURI': results['payload'][i]['custom']['permalink'],
			'maxLinks': extraParams['maxComments'],
			'extraParams': extraParams
		}

		toPrint = ''
		if( i%10 == 0 ):
			toPrint = '\t' + str(i) + ' of ' + str(size)

		jobsLst.append({
			'func': redditGetLinksFromComment,
			'args': keywords,
			'misc': i,
			'print': toPrint
		})

	print('\textracting comments - start')
	print('\tjobsLst.len:', len(jobsLst))
	resLst = parallelTask(jobsLst, threadCount=3)
	print('\tresLst.len:', len(resLst))
	print('\textracting comments - end')

	for res in resLst:
		res['output']['input-uri'] = res['input']['args']['commentURI']
		indx = res['misc']
		results['payload'][indx]['custom']['expanded-comments'] = res['output']

		#create link dist - start
		results['payload'][indx].setdefault('stats', {})
		results['payload'][indx]['stats'].setdefault('comments-link-dist', {})

		if( 'comments' not in res['output'] ):
			continue

		for comment in res['output']['comments']:
			linkCount = len(comment['links'])
			results['payload'][indx]['stats']['comments-link-dist'].setdefault(linkCount, 0)
			results['payload'][indx]['stats']['comments-link-dist'][linkCount] += 1
		#create link dist - end
	
	return results
	

def redditGetAllLinksFromCommentHTML(htmlStr, details=None):

	linksDict = {'links': []}
	lastIndex = -1

	while( True and htmlStr is not None ):
		
		link, lastIndex = getStrBetweenMarkers(htmlStr, 'href="', '"', startIndex=lastIndex+1)
		link = link.strip()

		if( len(link) != 0 ):
			if( link[0] == '/' ):
				link = 'https://www.reddit.com' + link

		if( lastIndex == -1 ):
			break
		elif( link.find('http') == 0 ):
			linksDict['links'].append( link )

	'''
	try:
		soup = BeautifulSoup(html.unescape(htmlStr), 'html.parser')
		allLinks = soup.find_all('a')

		
		for link in allLinks:
			if( link.has_attr('href') == False ):
				continue

			link = link['href'].strip()
			if( len(link) == 0 ):
				continue

			if( link[0] == '/' ):
				link = 'https://www.reddit.com' + link

			linksDict['links'].append( link )
	except:
		genericErrorInfo()
	'''

	if( details is None ):
		return linksDict['links']
	else:
		for key, val in details.items():
			linksDict[key] = val
	
	return linksDict

def redditKindTraslate(kind):
	
	kinds = {
		't1': 'comment',
		't2': 'account',
		't3': 'link',
		't4': 'message',
		't5': 'subreddit',
		't6': 'award'
	}

	if( kind in kinds ):
		return kinds[kind]
	else:
		return kind

def redditSetCommonDets(payload):

	result = {}
	try:

		result['pub-datetime'] = ''
		if( 'created_utc' in payload ):
			result['pub-datetime'] = datetime.utcfromtimestamp(payload['created_utc']).isoformat()
		
		commonAccessors = {
			'id': 'id',
			'parent_id': 'parent-id',
			'url': 'link',
			'title': 'title',
			'selftext': 'snippet',
			'body': 'text',
			'depth': 'depth'
		}

		for pubkey, privkey in commonAccessors.items():
			if( pubkey in payload ):
				result[privkey] = payload[pubkey]
			else:
				result[privkey] = ''

		if( result['depth'] == '' ):
			result['depth'] = -1

		result['depth'] += 1
		
		
		result['stats'] = {
			'score': -1,
			'comment-count': 0
		}

		if( 'score' in payload ):
			result['stats']['score'] = payload['score']

		if( 'num_comments' in payload ):
			result['stats']['comment-count'] = payload['num_comments']

		
		result['custom'] = {
			'author': payload['author'], 
			'subreddit': payload['subreddit'], 
			'permalink': 'https://www.reddit.com' + payload['permalink']
		}

	except:
		genericErrorInfo()

	return result

def redditAddComments(comment, allComments, maxi=-1, excludeCommentsWithNoLinks=True):

	if( maxi != -1 and len(allComments) >= maxi ):
		return False

	if( excludeCommentsWithNoLinks ):
		if( len(comment['links']) == 0 ):
			if( comment['link'].strip() != '' ):
				if( isSameLink(comment['link'], comment['custom']['permalink']) == False ):
					#add comments even though links in comments body is empty, because comments has a link that is not its permalink
					allComments.append(comment)	
		else:
			allComments.append(comment)
	else:
		allComments.append(comment)

	return True

def redditRecursiveTraverseComment(payload, tabCount, detailsDict, maxLinks=-1, extraParams=None):

	'''
		verify recursion, count links, dedup links
		patch links with just scheme incomplete
	'''

	if( extraParams is None ):
		extraParams = {}

	if( 'excludeCommentsWithNoLinks' not in extraParams ):
		extraParams['excludeCommentsWithNoLinks'] = True

	tab = '\t' * tabCount
	#print(tab, 'redditRecursiveTraverseComment():')
	
	if( 'kind' in payload ):

		if( payload['kind'] == 'Listing' ):
			
			#print(tab, 'kind: Listing')
			if( 'data' in payload ):
				redditRecursiveTraverseComment( payload['data'], tabCount + 1, detailsDict, maxLinks=maxLinks, extraParams=extraParams )

		elif( payload['kind'] == 't3' ):
			
			#print(tab, 'kind: t3 (link)')
			if( 'data' in payload ):
				if( 'selftext_html' in payload['data'] ):
					
					details = redditSetCommonDets(payload['data'])
					details['kind'] = redditKindTraslate('t3')
					comLinkDicts = redditGetAllLinksFromCommentHTML(payload['data']['selftext_html'], details)
					addFlag = redditAddComments( 
							comLinkDicts, 
							detailsDict['comments'], 
							maxLinks, 
							excludeCommentsWithNoLinks=extraParams['excludeCommentsWithNoLinks']
						)
					if( not addFlag ):
						return
		
		elif( payload['kind'] == 'LiveUpdate' ):
			
			if( 'data' in payload ):
				if( 'body_html' in payload['data'] ):
					
					details = redditSetCommonDets(payload['data'])
					details['kind'] = redditKindTraslate('live-update')
					comLinkDicts = redditGetAllLinksFromCommentHTML(payload['data']['body_html'], details)
					addFlag = redditAddComments( 
							comLinkDicts, 
							detailsDict['comments'], 
							maxLinks, 
							excludeCommentsWithNoLinks=extraParams['excludeCommentsWithNoLinks']
						)
					if( not addFlag ):
						return

		elif( payload['kind'] == 't1' ):
			
			#print(tab, 'kind: t1 (comment)')

			if( 'data' in payload ):

				if( 'body_html' in payload['data'] ):
					
					details = redditSetCommonDets(payload['data'])
					details['kind'] = redditKindTraslate('t1')
					comLinkDicts = redditGetAllLinksFromCommentHTML(payload['data']['body_html'], details)
					addFlag = redditAddComments( 
							comLinkDicts, 
							detailsDict['comments'], 
							maxLinks, 
							excludeCommentsWithNoLinks=extraParams['excludeCommentsWithNoLinks']
						)
					if( not addFlag ):
						return

			#comment with possible replies
				if( 'replies' in payload['data'] ): 
					if( len(payload['data']['replies']) != 0 ):
						redditRecursiveTraverseComment( payload['data']['replies'], tabCount + 1, detailsDict, maxLinks=maxLinks, extraParams=extraParams )#replies is a listing
	
	elif( 'children' in payload ):
		#print(tab, 'children')
		for child in payload['children']:
			redditRecursiveTraverseComment( child, tabCount + 1, detailsDict, maxLinks=maxLinks, extraParams=extraParams )

def redditPrlGetLinksFromComment(urisLst, maxLinks=-1, extraParams=None):

	urisLstSize = len(urisLst)
	if( urisLstSize == 0 ):
		return []

	if( extraParams is None ):
		extraParams = {}

	jobsLst = []
	for i in range(urisLstSize):
		keywords = {
			'commentURI': urisLst[i],
			'maxLinks': maxLinks,
			'extraParams': extraParams
		}

		toPrint = ''
		if( i%10 == 0 ):
			toPrint = '\t' + str(i) + ' of ' + str(urisLstSize)

		jobsLst.append({
			'func': redditGetLinksFromComment, 
			'args': keywords,
			'misc': False,
			'print': toPrint
		})

	resLst = parallelTask(jobsLst)
	for i in range(len(resLst)):

		resLst[i]['output']['input-uri'] = resLst[i]['input']['args']['commentURI']
		resLst[i] = resLst[i]['output']
	
	return resLst


def redditGetLinksFromComment(commentURI, maxLinks=-1, extraParams=None):

	print('\n\tredditGetLinksFromComment():')
	commentURI = commentURI.strip()
	if( len(commentURI) == 0 ):
		return {}

	if( extraParams is None ):
		extraParams = {}

	maxSleepInSeconds = 0
	if( 'maxSleep' in extraParams ):
		maxSleepInSeconds = extraParams['maxSleep']

	if( 'addRootComment' not in extraParams ):
		extraParams['addRootComment'] = False

	print('\taddRootComment:', extraParams['addRootComment'])

	detailsDict = {'comments': []}
	detailsDict['input-uri'] = commentURI


	try:
		#from: "https://www.reddit.com/r/worldnews/comments/5nv73m/former_mi6_agent_christopher_steeles_frustration/?ref=search_posts" 
		#to:   "https://www.reddit.com/r/worldnews/comments/5nv73m/former_mi6_agent_christopher_steeles_frustration.json?ref=search_posts"
		uriPath = urlparse(commentURI).path.strip()
		if( uriPath.endswith('/') ):
			commentURI = commentURI.replace(uriPath, uriPath[:-1] + '.json')
		else:
			commentURI = commentURI.replace(uriPath, uriPath + '.json')
	except:
		genericErrorInfo()
		return {}
	
	
	detailsDict['self'] = commentURI
	detailsDict['timestamp'] = getNowTime().replace('T', ' ')

	redditCommentJson = getDictFromJson( dereferenceURI(commentURI, maxSleepInSeconds) )
	payloadType = type(redditCommentJson)

	if( payloadType == dict ):		
		redditRecursiveTraverseComment( redditCommentJson, 1, detailsDict, maxLinks=maxLinks, extraParams=extraParams )	

	elif( payloadType == list ):
		
		if( len(redditCommentJson) != 2 ):
			print(' redditGetLinksFromComment(): unexpected size ' + str(len(redditCommentJson)) * 200)

		if( extraParams['addRootComment'] ):
			#this adds the parent as the root comment
			for commentThread in redditCommentJson:
				redditRecursiveTraverseComment( commentThread, 1, detailsDict, maxLinks=maxLinks, extraParams=extraParams )
		else:
			redditRecursiveTraverseComment( redditCommentJson[-1], 1, detailsDict, maxLinks=maxLinks, extraParams=extraParams )

	detailsDict['total-comments'] = len(detailsDict['comments'])
	
	return detailsDict
#reddit - end


#wikipedia - start
def wikipediaGetExternalLinksDictFromPage(pageURI, maxSleepInSeconds=0):

	print('\nwikipediaGetExternalLinksDictFromPage():')

	pageURI = pageURI.strip()
	if( len(pageURI) == 0 ):
		return {}

	if( getDomain(pageURI).find('wikipedia.org') == -1 ):
		return {}

	dedupSet = set()
	allLinksFromThisPage = {}
	htmlPage = dereferenceURI(URI=pageURI, maxSleepInSeconds=maxSleepInSeconds)
	soup = BeautifulSoup( htmlPage, 'html.parser' )
	

	'''
	#old logic to find references, unreliable
	allCitations = soup.findAll( 'div', {'class':'reflist'} )
	if( len(allCitations) == 0 ):
		return {}
	allCitations = allCitations[-1]
	'''

	#new logic to find reference
	allCitations = soup.find('', {'id':'References'} )
	if( allCitations is None ):
		return {}

	allCitations = allCitations.parent.find_next_sibling()	
	if( allCitations is None ):
		return {}

	allCitations.find_next_sibling()
	if( allCitations is None ):
		return {}



	allCitations = allCitations.findAll('li')
	print('\tallCitations:', len(allCitations))
	if( allCitations is None ):
		return {}
	

	allLinksFromThisPage['self'] = pageURI
	allLinksFromThisPage['links'] = []
	allLinksFromThisPage['timestamp'] = getNowTime().replace('T', ' ')
	
	for citation in allCitations:
		links = citation.findAll('a', {'rel':'nofollow'})
		for link in links:
			
			try:
				uri = link['href'].strip()
				if( uri[0] == '/' ):
					uri = 'http:' + uri

				URIR = getURIRFromMemento(uri)
				if( URIR == '' ):
					key = getDedupKeyForURI(uri)
				else:
					key = getDedupKeyForURI(URIR)

				if( key not in dedupSet ):
					
					dedupSet.add(key)
					count = len(allLinksFromThisPage['links'])
					
					if( URIR == '' ):
						tmp = {'link': uri, 'title': link.text.strip(), 'pos': count}
					else:
						tmp = {'link': URIR, 'memento': uri, 'title': link.text.strip(), 'pos': count}

					allLinksFromThisPage['links'].append( tmp )
					
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
def getDayOfWeek(dateObj):
	if( isinstance(dateObj, datetime) == False ):
		return ''
	
	weekdayDict = {
		0: 'monday',
		1: 'tuesday',
		2: 'wednesday',
		3: 'thursday',
		4: 'friday',
		5: 'saturday',
		6: 'sunday'
	}
	
	return weekdayDict[dateObj.weekday()]


def parallelProxy(job):
	
	output = job['func'](**job['args'])

	if( 'print' in job ):
		if( len(job['print']) != 0 ):
			print(job['print'])

	return {'input': job, 'output': output, 'misc': job['misc']}

'''
	jobsLst: {
				'func': function,
				'args': {functionArgName0: val0,... functionArgNamen: valn}
				'misc': ''
			 }
	
	usage example:
	jobsLst = []
	keywords = {'uri': 'http://www.odu.edu'}
	jobsLst.append( {'func': getDedupKeyForURI, 'args': keywords} )

	keywords = {'uri': 'http://www.cnn.com'}
	jobsLst.append( {'func': getDedupKeyForURI, 'args': keywords} )

	keywords = {'uri': 'http://www.arsenal.com'}
	jobsLst.append( {'func': getDedupKeyForURI, 'args': keywords} )

	print( parallelTask(jobsLst) )
'''
def parallelTask(jobsLst, threadCount=5):

	if( len(jobsLst) == 0 ):
		return []

	if( threadCount < 2 ):
		threadCount = 2

	try:
		workers = Pool(threadCount)
		resLst = workers.map(parallelProxy, jobsLst)

		workers.close()
		workers.join()
	except:
		genericErrorInfo()
		return []

	return resLst

def genericParseDate(dateStr):
	from dateutil.parser import parse
	
	dateStr = dateStr.strip()
	if( len(dateStr) == 0 ):
		return None

	try:
		dateObj = parse(dateStr)
		return dateObj
	except:
		#genericErrorInfo()
		pass

	return None

def wholeWordFind(key, source):

	res = re.search(r'\b' + re.escape(key) + r'\b', source)
	if( res ):
		return res.start()
	else:
		return -1


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
		return dataList	

	minVal = min(dataList)
	maxVal = max(dataList)
	denom = maxVal - minVal

	if( denom == 0 ):
		return dataList

	for i in range(len(dataList)):
		dataList[i] = (dataList[i] - minVal) / denom
	
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
		#print('\toffending text:', output, '\n')
	
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

	import statistics

	if( len(numList) < 2 ):
		return {}

	numList.sort()

	summaryStatsDict = {}
	quarts = quartiles(numList, False)

	summaryStatsDict['minimum'] = numList[0]
	summaryStatsDict['lower-quartile'] = quarts[0]
	summaryStatsDict['median'] = quarts[1]
	summaryStatsDict['upper-quartile'] = quarts[2]
	summaryStatsDict['maximum'] = numList[-1]

	summaryStatsDict['mean'] = statistics.mean(numList)
	summaryStatsDict['range'] = summaryStatsDict['maximum'] - summaryStatsDict['minimum']
	summaryStatsDict['count'] = len(numList)
	summaryStatsDict['pstdev'] = statistics.pstdev( numList )


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

def sleepCountDown(seconds):
	for i in range(seconds, 0, -1):
		time.sleep(1)
		sys.stdout.write(str(i)+' ')
		sys.stdout.flush()
	print()

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
			
			googleHTMLPage = googleGetHTMLPage(searchString=query, page=page, seleniumFlag=seleniumFlag)
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
def getPayloadDetails(title, crawlDatetime, snippet, rank, page, custom=None):
	
	if( custom is None ):
		custom = {}

	return {
		'title': title, 
		'crawl-datetime': crawlDatetime, 
		'snippet': snippet, 
		'rank': rank,
		'page': page,
		'custom': custom
	}

def addMoreLinks(elm, rank, payload, page):
	
	moreLinks = elm.findAll('a')
	subrank = 1

	for moreLink in moreLinks:

		domain = ''
		if( moreLink.has_attr('href') ):
			domain = getDomain( moreLink['href'] )
		
		if( domain.find('google.com') != -1 or domain.find('googleusercontent.com') != -1 ):
			#skip empty and google links
			continue
		
		link = ''
		if( moreLink.has_attr('data-href') ):
			link = moreLink['data-href']
		elif( moreLink.has_attr('href') ):
			link = moreLink['href']

		if( link in payload or len(link) == 0 ):
			continue
		
		if( link.find('http') != 0 ):
			continue

		title = moreLink.text.strip()
		if( len(title) != 0 ):
			locRank = str(rank) + '.' + str(subrank)
			
			#print('\t\tlink:', link)
			#print('\t\t\t', title)
			
			custom = {'extra-link': True}
			payload[link] = getPayloadDetails(
				title=title, 
				crawlDatetime='', 
				snippet='', 
				rank=float(locRank),
				page=page,
				custom=custom
			)
			
			subrank += 1


def googleRetrieveLinksFromPage(googleHTMLSoup, rankAdditiveFactor=0, page=1):

	if( len(googleHTMLSoup) ==  0 ):
		return {}

	#linksDict format: {link, [crawlDatetime|nowDatetime]}
	linksDict = {}
	rank = 0
	results = []

	for possibleClasses in ['med', 'srg']:
		results = googleHTMLSoup.findAll('div', {'class': possibleClasses})
		if( len(results) != 0 ):
			break

	for result in results:

		liOrDiv = result.findAll('li', {'class': 'g'})
		if( len(liOrDiv) == 0 ):
			liOrDiv = result.findAll('div', {'class': 'g'})

		for resultInstance in liOrDiv:

			if( resultInstance.h3 == None ):
				#attempt to get more links
				addMoreLinks(resultInstance, rank, linksDict, page)
				continue

			crawlDateTime = resultInstance.find('span', {'class':'f'})
			for possibleTag in ['span', 'div']:
				snippet = resultInstance.find(possibleTag, {'class':'st'})
				if( snippet is not None ):
					break


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

			title = resultInstance.h3.a.text
			titleLink = resultInstance.h3.a['href']
			titleLink = titleLink.strip()

			if( titleLink.find('http') != 0 ):
				continue


			#attempt to get more links
			addMoreLinks(resultInstance, rank, linksDict, page)

			'''
			linksDict format:
			{
				'link': {'title': '', 'crawl-datetime': '', 'snippet': ''}
				...
			}
			'''
			
			rank += 1
			linksDict[titleLink] = getPayloadDetails(
				title=title, 
				crawlDatetime=crawlDateTime, 
				snippet=snippet, 
				rank=rank+rankAdditiveFactor,
				page=page
			)
		#attempt to add even more links
		addMoreLinks(result, rank, linksDict, page)

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

def getLinks(uri='', html='', commaDelDomainsToExclude='', fromMainTextFlag=True, extraParams=None):

	'''
	uri = uri.strip()
	if( len(uri) == 0 ):
		return []
	'''
	if( extraParams is None ):
		extraParams = {}

	uri = uri.strip()
	if( len(uri) != 0 ):
		if( uri[-1] != '/' ):
			uri = uri + '/'

	sleepSeconds = 3
	if( 'sleepSeconds' in extraParams ):
		sleepSeconds = extraParams['sleepSeconds']

	domainsToExcludeDict = {}
	for domain in commaDelDomainsToExclude.split(','):
		domain = domain.strip()
		domainsToExcludeDict[domain] = True

	allLinks = []
	dedupDict = {}
	try:
		if( len(html) == 0 ):

			html = dereferenceURI(uri, sleepSeconds)
		
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

def derefURICache(uri, cacheFolder='', lookupCache=True):

	uri = uri.strip()
	cacheFolder = cacheFolder.strip()

	if( len(uri) == 0 ):
		return ''

	if( len(cacheFolder) == 0 ):
		cacheFolder = './html-cache/'

	if( cacheFolder[-1] != '/' ):
		cacheFolder = cacheFolder + '/'

	createFolderAtPath(cacheFolder)
	uriFilename = cacheFolder + getURIHash(uri) + '.html'

	if( os.path.exists(uriFilename) and lookupCache ):
		html = readTextFromFile(uriFilename)
		html = html.strip()
		if( len(html) != 0 ):
			return html
	
	html = dereferenceURI( uri, 0 )
	html = html.strip()
	if( len(html) != 0 ):
		writeTextToFile(uriFilename, html)
	
	return html

def dereferenceURI(URI, maxSleepInSeconds=5, extraParams=None):
	
	#print('dereferenceURI():', URI)
	URI = URI.strip()
	if( len(URI) == 0 ):
		return ''

	if( extraParams is None ):
		extraParams = {}
	
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

		extraParams.setdefault('sizeRestrict', 4000000)
		htmlPage = mimicBrowser(URI, extraParams=extraParams)
	except:
		genericErrorInfo()
	
	return htmlPage

def naiveChkHTML(uri):

	uri = uri.strip()
	if( len(uri) == 0 ):
		return True

	exn = [
		'tif', 
		'tiff', 
		'gif', 
		'jpeg', 
		'jpg', 
		'jif', 
		'jfif',
		'jp2', 
		'jpx', 
		'j2k', 
		'j2c',
		'fpx',
		'pcd',
		'png',
		'pdf',
		'mp3',
		'mp4'
	]
	
	scheme, netloc, path, params, query, fragment = urlparse( uri )
	path = path.split('.')[-1].lower().replace('/', '')

	if( path in exn ):
		return False
	else:
		return True

def getMimeEncType(uri):
	
	uri = uri.strip()

	if( len(uri) == 0 ):
		return ('', None)

	if( naiveChkHTML(uri) ):
		return ('text/html', None)
	
	mime = MimeTypes()
	mime = mime.guess_type(uri)

	if( mime is None ):
		return ('', None)
	else:
		return mime

def getDomain(url, includeSubdomain=True, excludeWWW=True):

	url = url.strip()
	if( len(url) == 0 ):
		return ''

	if( url.find('http') == -1  ):
		url = 'http://' + url

	domain = ''
	
	try:
		ext = extract(url)
		
		domain = ext.domain.strip()
		subdomain = ext.subdomain.strip()
		suffix = ext.suffix.strip()

		if( len(suffix) != 0 ):
			suffix = '.' + suffix 

		if( len(domain) != 0 ):
			domain = domain + suffix
		
		if( excludeWWW ):
			if( subdomain.find('www') == 0 ):
				if( len(subdomain) > 3 ):
					subdomain = subdomain[4:]
				else:
					subdomain = subdomain[3:]


		if( len(subdomain) != 0 ):
			subdomain = subdomain + '.'

		if( includeSubdomain ):
			domain = subdomain + domain
	except:
		genericErrorInfo()
		return ''

	return domain

#http://stackoverflow.com/questions/4770297/python-convert-utc-datetime-string-to-local-datetime
# From 2015-07-12 18:45:11
def datetime_from_utc_to_local(utc):
	epoch = time.mktime(utc.timetuple())
	offset = datetime.fromtimestamp (epoch) - datetime.utcfromtimestamp (epoch)
	return utc + offset

def parseStrDate(strDate):

	try:
		return parseDateStr(strDate)
	except:
		genericErrorInfo()

	return None

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

def makeHeadRequest(uri, extraParams=None):
	return mimicBrowser(uri, getRequestFlag=False, extraParams=extraParams)

def mimicBrowser(uri, getRequestFlag=True, extraParams=None):
	
	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''

	if( extraParams is None ):
		extraParams = {}

	extraParams.setdefault('timeout', 10)
	extraParams.setdefault('sizeRestrict', -1)

	try:
		headers = getCustomHeaderDict()
		response = ''

		if( getRequestFlag ):
			response = requests.get(uri, headers=headers, timeout=extraParams['timeout'])#, verify=False
			
			if( extraParams['sizeRestrict'] != -1 ):
				if( 'Content-Length' in response.headers ):
					if( int(response.headers['Content-Length']) > extraParams['sizeRestrict'] ):
						return 'Exceeded size restriction: ' + str(extraParams['sizeRestrict'])
					
			return response.text
		else:
			response = requests.head(uri, headers=headers, timeout=extraParams['timeout'])#, verify=False
			response.headers['status-code'] = response.status_code
			return response.headers
	except:

		genericErrorInfo()
		print('\tquery is: ', uri)
		if( getRequestFlag == False ):
			return {}
	
	return ''

def genericErrorInfo(errOutfileName='', errPrefix=''):
	exc_type, exc_obj, exc_tb = sys.exc_info()
	fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
	errorMessage = fname + ', ' + str(exc_tb.tb_lineno)  + ', ' + str(sys.exc_info())
	print('\tERROR:', errorMessage)
	
	mode = 'w'
	if( os.path.exists(errOutfileName) ):
		mode = 'a'

	if( len(errPrefix) != 0 ):
		errPrefix = errPrefix + ': '

	errOutfileName = errOutfileName.strip()
	if( len(errOutfileName) != 0 ):
		outfile = open(errOutfileName, mode)
		outfile.write(getNowFilename() + '\n')
		outfile.write('\t' + errPrefix + errorMessage + '\n')
		outfile.close()

	return  sys.exc_info()
	

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

	#credit for list: https://support.tigertech.net/index-file-names
	defaultIndexNames = [
		'index.html',
		'index.htm',
		'index.shtml',
		'index.php',
		'index.php5',
		'index.php4',
		'index.php3',
		'index.cgi',
		'default.html',
		'default.htm',
		'home.html',
		'home.htm',
		'Index.html',
		'Index.htm',
		'Index.shtml',
		'Index.php',
		'Index.cgi',
		'Default.html',
		'Default.htm',
		'Home.html',
		'Home.htm',
		'placeholder.html'
	]

	if( uri[-1] == '/' ):
		uri = uri[:-1]

	try:
		components = urlparse(uri)
		path = components.path.split('/')

		if( len(path) == 2 and path[-1] in set(defaultIndexNames) ):
			return 0
		else:
			return len(path) - 1
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

def getPageTitle(uri, html='', maxSleepInSeconds=0):

	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''

	title = ''
	try:
		if( len(html) == 0 ):
			html = dereferenceURI(uri, maxSleepInSeconds=maxSleepInSeconds)

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

#uri - start

def dedupLinks(uriLst):

	prev = len(uriLst)

	dedupSet = set()
	dedupedLst = []
	for u in uriLst:
		uriKey = getDedupKeyForURI(u)

		if( uriKey in dedupSet ):
			continue

		dedupSet.add( uriKey )
		dedupedLst.append(u)

	print('\tdedupLinks(): diff', prev - len(dedupedLst))

	return dedupedLst


def isSameLink(left, right):
	return getDedupKeyForURI(left) == getDedupKeyForURI(right)

def naiveIsURIShort(uri):

	specialCases = []

	try:
		scheme, netloc, path, params, query, fragment = urlparse( uri )
		if( netloc in specialCases ):
			return True

		path = path.strip()
		if( len(path) != 0 ):
			if( path[0] == '/' ):
				path = path[1:]

		path = path.split('/')
		if( len(path) > 1 ):
			#path length exceeding 1 is not considered short
			return False

		tld = extract(uri).suffix
		tld = tld.split('.')
		if( len(tld) == 1 ):
			#e.g., tld = 'com', 'ly'
			#short: http://t.co (1 dot) not news.sina.cn (2 dots)
			if( len(tld[0]) == 2 and netloc.count('.') == 1 ):
				return True
		else:
			#e.g., tld = 'co.uk'
			return False
	except:
		genericErrorInfo()

	return False

def seleniumLoadPageScrollToEnd(driver, uri, closeBrowerFlag=True, maxScroll=20, extraParams=None):
	print('seleniumLoadWebpage():')

	uri = uri.strip()
	if( len(uri) == 0 ):
		return {}

	html = ''
	output = {}
	try:
		driver.get(uri)
		prevLength = len(driver.page_source)
		
		print('\tprevLength:', prevLength)
		print('\tscrolling')
		
		driver.execute_script('window.scrollTo(0, document.body.scrollHeight);')
		randSleep()
		scrollCount = 0

		if( 'stopHandler' in extraParams and 'stopHandlerParams' in extraParams ):
			
			while( True ):
				#expects manual exit or result['stop'] trigger whichever comes first
				scrollCount += 1
				prevLength = len(driver.page_source)
				driver.execute_script('window.scrollTo(0, document.body.scrollHeight);')
			
				print('\tcurLen-prevlen:', len(driver.page_source) - prevLength)
				randSleep()
				result = extraParams['stopHandler']( driver.page_source.encode('utf-8'), extraParams['stopHandlerParams'] )
				output = result
				print('\toutputsize:', len(result['output']))

				if( result['stop'] ):
					print('\tstopHandler has initiated stop, stopping')
					return result
		else:

			while( len(driver.page_source) > prevLength and scrollCount != maxScroll ):
				scrollCount += 1
				prevLength = len(driver.page_source)
				driver.execute_script('window.scrollTo(0, document.body.scrollHeight);')
			
				print('\tcurLen-prevlen:', len(driver.page_source) - prevLength)
				print('\tscrolling:', scrollCount, 'of', maxScroll)

				randSleep()

		output['html'] = driver.page_source.encode('utf-8')
		if( closeBrowerFlag ):
			driver.quit()
	except:
		genericErrorInfo()
		return output

	print('\tlast return')
	return output

def seleniumLoadWebpage(driver, uri, waitTimeInSeconds=10, closeBrowerFlag=True, extraParams=None):
	print('seleniumLoadWebpage():')

	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''
	html = ''

	if( extraParams is None ):
		extraParams = {}

	#directive: consider phantom js but set header
	try:
		print('\tgetting:', uri)

		driver.get(uri)
		'''
			this statement
			driver.maximize_window()
			unknown error: cannot get automation extension\nfrom unknown error
		'''

		if( waitTimeInSeconds > 0 ):
			print('\tsleeping in seconds:', waitTimeInSeconds)
			time.sleep(waitTimeInSeconds)

		if( 'script' in extraParams ):
			driver.execute_script( extraParams['script'] )

		html = driver.page_source.encode('utf-8')
		
		if( closeBrowerFlag ):
			driver.quit()
	except:
		genericErrorInfo()
		return ''

	return html

def nodeLoadWebpage(uri, throttleSeconds=3):
	
	print('\nnodeLoadWebpage():')

	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''
	html = ''

	try:
		print('\tgetting:', uri)

		if( throttleSeconds > 0 ):
			print('\tthrottleSeconds:', throttleSeconds)
			time.sleep(throttleSeconds)
		
		html = check_output([workingFolder() + 'nodejs-client/browser.js', uri])
		html = html.decode('utf-8')
	except:
		genericErrorInfo()
		return ''

	return html

def seleniumScreenShotCommon(driver, outfilename, extraParams):

	driver.save_screenshot(outfilename)
	print('\tsaved screenshot:', outfilename)

	if( 'closeBrower' in extraParams ):
		if( extraParams['closeBrower'] ):
			driver.quit()


def seleniumSaveScreenshot(driver, uri, outfilename, waitTimeInSeconds=10, extraParams=None):
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

	if( extraParams is None ):
		extraParams = {}

	
	#directive: consider phantom js but set header
	#driver = webdriver.PhantomJS()
	try:
		#driver = webdriver.Firefox()
		print('\tgetting:', uri)
		driver.get(uri)

		if( 'windowWidth' in extraParams and 'windowHeight' in extraParams ):
			driver.set_window_size(extraParams['windowWidth'], extraParams['windowHeight'])
		else:
			driver.maximize_window()

		if( 'script' in extraParams ):
			driver.execute_script( extraParams['script'] )

	
		print('\tpre sleeping in seconds:', waitTimeInSeconds)
		time.sleep(waitTimeInSeconds)
		seleniumScreenShotCommon(driver, outfilename, extraParams)

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

def carbonDateIsServerOn(host='localhost', port='8888'):

	try:
		response = requests.head('http://' + host +':' + port + '/')
		
		if( response.status_code == 200 ):
			return True
		else:
			return False

	except:
		genericErrorInfo()

	return False

def useCarbonDateServer(uri, host='localhost', port='8888'):

	uri = uri.strip()
	port = str(port)

	if( len(uri) == 0 ):
		return ''

	try:
		output = check_output(['curl', '--silent', 'http://' + host +':' + port + '/cd/' + uri])
		output = output.decode('utf-8')
		output = json.loads(output)
		
		if( output['uri'] == uri ):
			return output['estimated-creation-date']
		else:
			return ''
	except:
		genericErrorInfo()

	return ''


def carbonDateServerStartStop(msg='start', extraParams=None):

	if( extraParams is None ):
		extraParams = {}

	if( 'port' in extraParams ):
		port = extraParams['port']
	else:
		port = '8888'


	if( msg =='start' and carbonDateIsServerOn(port=port) ):
		print('\tCD Server already on - no-op')
		return

	print('\tStarting CD Server')
	flags = []
	allFlags = []

	if( 'excludeBacklinks' not in extraParams ):
		extraParams['excludeBacklinks'] = True

	if( 'excludeArchives' not in extraParams ):
		extraParams['excludeArchives'] = False

	if( 'excludeGoogle' not in extraParams ):
		extraParams['excludeGoogle'] = False

	



	if( extraParams['excludeBacklinks'] ):
		allFlags.append('cdGetBacklinks')

	if( extraParams['excludeArchives'] ):
		allFlags.append('cdGetArchives')

	if( extraParams['excludeGoogle'] ):
		allFlags.append('cdGetGoogle')

	if( len(allFlags) != 0 ):
		flags = '-e ' + ' '.join(allFlags)
		flags = flags.split(' ')

	try:
		if( msg == 'start' ):
			request = [
				'docker', 
				'run', 
				'--rm', 
				'-d', 
				'-p', 
				port + ':' + port, 
				'--name',
				'carbondateserver',
				'oduwsdl/carbondate', 
				'./main.py', 
				'-s'] + flags
			check_output(request)
		else:
			check_output(['docker', 'rm', '-f', 'carbondateserver'])
	except:
		genericErrorInfo()


def useCarbonDate(URI, excludeBacklinks=False, excludeArchives=False, port='7777', extraParams=None):

	flags = []
	allFlags = []

	if( extraParams is None ):
		extraParams = {}
	
	if( 'excludeGoogle' not in extraParams ):
		extraParams['excludeGoogle'] = False

	if( excludeBacklinks ):
		allFlags.append('cdGetBacklinks')

	if( excludeArchives ):
		allFlags.append('cdGetArchives')

	if( extraParams['excludeGoogle'] ):
		allFlags.append('cdGetGoogle')


	if( len(allFlags) != 0 ):
		flags = '-e ' + ' '.join(allFlags)
		flags = flags.split(' ')


	request = ['docker', 'run', '-it', '-p', port + ':' + port, 'oduwsdl/carbondate', './main.py', '-l', URI] + flags

	try:
		output = check_output(request)
		output = output.decode('utf-8')
		output = json.loads(output)
		
		if( output['uri'] == URI ):
			return output['estimated-creation-date']
		else:
			return ''

	except:
		genericErrorInfo()

	return ''

def isArchived(uri, mementoAggregator='http://memgator.cs.odu.edu/'):

	print('\n\tisArchived():')
	print('\t\turi:', uri)
	uri = uri.strip()
	mementoAggregator = mementoAggregator.strip()

	if( len(uri) == 0 or len(mementoAggregator) == 0 ):
		print('\tBad request uri or mementoAggregator')
		return False

	#all mementos are archived
	if( len(getURIRFromMemento(uri)) != 0 ):
		print('\t\turi-r extracted from memento link:', uri)
		return True

	if( getMementoCount(uri, mementoAggregator) > 0 ):
		return True
	else:
		return False

	'''
		#directive: get mementoAggregator from config
		output = ''
		try:
			output = check_output(['curl', '-I', '--silent', '-m', '20', mementoAggregator + 'timemap/json/' + uri])
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

def getMementoCount(uri, mementoAggregator='http://memgator.cs.odu.edu/', timeout='20'):

	print('\tgetMementoCount():', uri)
	#print('\tmementoAggregator:', mementoAggregator)
	#print('\ttimeout', timeout)

	uri = uri.strip()
	mementoAggregator = mementoAggregator.strip()

	if( len(uri) == 0 or len(mementoAggregator) == 0 ):
		print('\t\tBad request uri or mementoAggregator')
		return -1

	#directive: get mementoAggregator from config
	output = ''
	mementoCount = 0
	try:
		output = check_output(['curl', '-I', '--silent', '-m', str(timeout), mementoAggregator + 'timemap/json/' + uri])
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

def getDedupKeyForURI(uri):

	uri = uri.strip()
	if( len(uri) == 0 ):
		return ''

	exceptionDomains = ['www.youtube.com']

	try:
		scheme, netloc, path, params, query, fragment = urlparse( uri )
		
		netloc = netloc.strip()
		path = path.strip()
		optionalQuery = ''

		if( len(path) != 0 ):
			if( path[-1] != '/' ):
				path = path + '/'

		if( netloc in exceptionDomains ):
			optionalQuery = query.strip()

		return netloc + path + optionalQuery
	except:
		print('Error uri:', uri)
		genericErrorInfo()

	return ''

def expanUrlSecondTry(url, curIter=0, maxIter=100):

	'''
	Attempt to get first good location. For defunct urls with previous past
	'''

	url = url.strip()
	if( len(url) == 0 ):
		return ''

	if( maxIter % 10 == 0 ):
		print('\t', maxIter, ' expanUrlSecondTry(): url - ', url)

	if( curIter>maxIter ):
		return url


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

			return expanUrlSecondTry(redirectUrl, curIter+1, maxIter)
		else:
			return url

	except:
		print('\terror url:', url)
		genericErrorInfo()
	

	return url

def expandUrl(url, secondTryFlag=True, timeoutInSeconds='10'):

	#print('\tgenericCommon.py - expandUrl():', url)
	#http://tmblr.co/ZPYSkm1jl_mGt, http://bit.ly/1OLMlIF
	timeoutInSeconds = str(timeoutInSeconds)
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
		output = output.decode('utf-8')
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
					#if( url[-1] == '/' ):
					#	url = url[:-1]
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
	except Exception as e:
		#Part B: returns the lasts good url if the last response is not a 200.
		print('\terror url:', url)
		print(e)
		#genericErrorInfo()

		
		
		if( secondTryFlag ):
			print('\tsecond try')
			return expanUrlSecondTry(url)
		else:
			return url

#uri - end

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

class DocVect(object):

	translator = str.maketrans({key: None for key in string.punctuation})

	@staticmethod
	def buildLexicon(corpus, stopwordsFlag=True, stemFlag=True, punctuationFlag=True):
		from nltk.stem.porter import PorterStemmer

		stopwordsDict = getStopwordsDict()
		lexicon = []
		dedupDict = {}

		for doc in corpus:
			doc = doc.split()

			for word in doc:

				if( punctuationFlag ):
					#word = removeSomePunctuations(word)
					word = word.translate(DocVect.translator)

				word = word.lower()

				if( stopwordsFlag ):
					if( word in stopwordsDict ):
						continue

				if( stemFlag ):
					stemmer = PorterStemmer()
					word = stemmer.stem(word)

				if( word not in dedupDict ):
					lexicon.append(word)
					dedupDict[word] = True

		return lexicon

	@staticmethod
	def getTFDict(tfVector, sortedVocab):

		if( len(tfVector) != len(sortedVocab) ):
			return {}

		singleTFDict = {}

		for i in range( len(sortedVocab) ):
			vocab, vocabDet = sortedVocab[i]
			singleTFDict[vocab] = tfVector[i]
			

		return singleTFDict

	@staticmethod
	def getDocVector(document, vocabulary):
		return [DocVect.tf(word, document) for word in vocabulary]

	@staticmethod
	def getIDFMatrix(docList, vocabulary):
		idfVector = [DocVect.idf(word, docList) for word in vocabulary]
		#return idfVector
		return DocVect.buildIDFMatrix(idfVector)

	@staticmethod
	def getDocTermMatrix_obsolete(docList, vocab):
		
		if( len(docList) == 0 or len(vocab) == 0 ):
			return []

		'''
			docList: ['Julie loves me more than Linda loves me',
			'Jane likes me more than Julie loves me',
			'He likes basketball more than baseball']

			vocab: [Julie, loves, me, more, than, Linda, Jane, likes, He, basketball, baseball]
		'''

		docTermMatrix = []
		for doc in docList:

			#tfVector': [1, 2, 2, 1, 1, 1, 0, 0, 0, 0, 0]
			tfVector = DocVect.getDocVector(doc, vocab)
			docTermMatrix.append(tfVector)

		return docTermMatrix

	@staticmethod
	def getNgram(docList, ngram, token_pattern=r'(?u)\b\w\w+\b'):

		countVectorizer = CountVectorizer(stop_words='english', token_pattern=token_pattern, ngram_range=(ngram, ngram))
		termFreqMatrix = countVectorizer.fit_transform(docList).toarray()
		
		return countVectorizer.vocabulary_

	@staticmethod
	def getDocTermMatrixAndVocab(docList, ngramRange=(1,1)):
		
		if( len(docList) == 0 ):
			return []

		'''
			docList: ['Julie loves me more than Linda loves me',
			'Jane likes me more than Julie loves me',
			'He likes basketball more than baseball']

			vocab: [Julie, loves, me, more, than, Linda, Jane, likes, He, basketball, baseball]
		'''

		count_vectorizer = CountVectorizer( min_df=1, stop_words='english', ngram_range=ngramRange )
		term_freq_matrix = count_vectorizer.fit_transform(docList)
		
		return {'mat': term_freq_matrix.todense(), 'vocab': list(count_vectorizer.vocabulary_.keys()) }
		

	@staticmethod
	def getNormalizedTFIDFMatrixFromDocList_dev(docList):

		vocabulary = DocVect.buildLexicon(docList, stopwordsFlag=True, stemFlag=True, punctuationFlag=True)

		prevNow = datetime.now()
		idfMatrix = DocVect.getIDFMatrix(docList, vocabulary)
		delta = datetime.now() - prevNow
		print('\tdelta getIDFMatrix seconds:', delta.seconds)

		prevNow = datetime.now()
		docTermMatrix = DocVect.getDocTermMatrix(docList, vocabulary)
		delta = datetime.now() - prevNow
		print('\tdelta getDocTermMatrix seconds:', delta.seconds)

		return DocVect.getNormalizedTFIDFMatrix(docTermMatrix, idfMatrix)

	#credit: https://sites.temple.edu/tudsc/2017/03/30/measuring-similarity-between-texts-in-python/ - start
	@staticmethod
	def stemTokens(tokens):
		from nltk.stem.porter import PorterStemmer
		stemmer = PorterStemmer()
		return [stemmer.stem(token) for token in tokens]

	@staticmethod
	def stemNormalize(text):
		from nltk.tokenize import word_tokenize#prerequisite is single use of  nltk.download('punkt') # first-time use only

		remove_punct_dict = dict((ord(punct), None) for punct in string.punctuation)
		text = text.lower()
		text = text.translate(remove_punct_dict)
		text = word_tokenize(text)
		
		return DocVect.stemTokens(text)

	@staticmethod
	def lemTokens(tokens):
		from nltk.stem import WordNetLemmatizer#prerequisite is single use of nltk.download('wordnet')
		lemmer = WordNetLemmatizer()
		return [lemmer.lemmatize(token) for token in tokens]

	@staticmethod
	def lemNormalize(text):
		from nltk.tokenize import word_tokenize#prerequisite is single use of  nltk.download('punkt') # first-time use only
		remove_punct_dict = dict((ord(punct), None) for punct in string.punctuation)
		
		text = text.lower().translate(remove_punct_dict)
		text = word_tokenize(text)

		return DocVect.lemTokens(text)

	#credit: https://sites.temple.edu/tudsc/2017/03/30/measuring-similarity-between-texts-in-python/ - end
	@staticmethod
	def getTFMatrixFromDocList(oldDocList, params=None):

		if( len(oldDocList) == 0 ):
			return []

		docList = []
		#remove empty documents
		for i in range(len(oldDocList)):
			if( len(oldDocList[i]) != 0 ):
				docList.append( oldDocList[i] )

		if( len(docList) == 0 ):
			return []

		if( params is None ):
			params = {}

		
		params.setdefault('IDF', {'active': False, 'norm': None})
		params['IDF'].setdefault('active', False)
		params['IDF'].setdefault('norm', None)#see TfidfTransformer for options

		params.setdefault('normalize', False)#normalize TF by vector norm (L2 norm)
		params.setdefault('ngram-range', (1, 1))#normalize TF by vector norm (L2 norm)
		params.setdefault('tokenizer', None)
		params.setdefault('verbose', False)
				
		np.set_printoptions(threshold=np.nan, linewidth=100)
		from sklearn.feature_extraction.text import CountVectorizer
		from sklearn.feature_extraction.text import TfidfTransformer
		from sklearn.preprocessing import normalize

		count_vectorizer = CountVectorizer(tokenizer=params['tokenizer'], stop_words='english', ngram_range=params['ngram-range'])
		term_freq_matrix = count_vectorizer.fit_transform(docList)
		
		#sortedVocab = sorted(count_vectorizer.vocabulary_.items(), key=lambda x: x[1])
		#print('sortedVocab:', sortedVocab)

		if( params['normalize'] ):
			term_freq_matrix = normalize(term_freq_matrix, norm='l2', axis=1)

		if( params['IDF']['active'] ):
			tfidf = TfidfTransformer( norm=params['IDF']['norm'] )
			tfidf.fit(term_freq_matrix)

			tf_idf_matrix = tfidf.transform(term_freq_matrix)
			dense = tf_idf_matrix.todense()
		else:
			dense = term_freq_matrix.todense()
		
		if( params['verbose'] ):
			print('\nDENSE matrix')
			print(dense)
		else:
			#print('\tgetTFMatrixFromDocList(): not printing dense')
			pass
			

		dense = dense.tolist()
		if( 'extra-payload' in params ):
			
			vocabDict = {}
			for vocab, pos in count_vectorizer.vocabulary_.items():
				vocabDict.setdefault(vocab, {'TF': 0})

				for row in dense:
					vocabDict[vocab]['TF'] += row[pos]

			return {
				'TF-Mat': dense,
				'vocab': sorted(vocabDict.items(), key=lambda x: x[1]['TF'], reverse=True)
			}
		else:
			return dense

	@staticmethod
	def getNormalizedTFIDFMatrixFromDocList(docList, ngramRange=(1,1), tokenizer=None):
		
		#np.set_printoptions(threshold=np.nan, linewidth=110)
		'''
			Preprocessing notes:
			stopwords not removed
			lowercased
			for more see:
				http://scikit-learn.org/stable/modules/generated/sklearn.feature_extraction.text.CountVectorizer.html#sklearn.feature_extraction.text.CountVectorizer
			vs 

			story graph preprocessing:
			Lowercased
			Removal of punctuation
			Removal of stopwords
			Not tokenized
				datetimes and percent and money
		'''
		from sklearn.feature_extraction.text import CountVectorizer
		from sklearn.feature_extraction.text import TfidfTransformer

		count_vectorizer = CountVectorizer(stop_words='english', ngram_range=ngramRange)
		term_freq_matrix = count_vectorizer.fit_transform(docList)
		
		#print(term_freq_matrix.todense())

		#debug - start
		'''
			print('\n\nVocabulary:', count_vectorizer.vocabulary_, '\n')
			sortedVocab = sorted(count_vectorizer.vocabulary_.items(), key=lambda x: x[1], reverse=True)
			print( '\nVocab:' )
			for tup in sortedVocab:
				print(tup, end='')
			print()
		'''
		#debug - end

		tfidf = TfidfTransformer(norm='l2')
		tfidf.fit(term_freq_matrix)

		tf_idf_matrix = tfidf.transform(term_freq_matrix)
		return tf_idf_matrix.todense().tolist()

	@staticmethod
	def getNormalizedTFIDFMatrix(doc_term_matrix, my_idf_matrix):
		
		doc_term_matrix_tfidf = []
		#performing tf-idf matrix multiplication, then normalizing
		for tf_vector in doc_term_matrix:
			tf_idf_vector = np.dot(tf_vector, my_idf_matrix)
			doc_term_matrix_tfidf.append(DocVect.l2_normalizer(tf_idf_vector))
		
		return doc_term_matrix_tfidf

	@staticmethod
	def add0sToMainDiag(squareMat):
		
		row, col = squareMat.shape
		if( row != col ):
			return 
		for i in range(row):
			squareMat[i][i] = 0



	@staticmethod
	def getColSimScore(normalizedTFIDFMatrix, simMatInput=False):
			
		if( len(normalizedTFIDFMatrix) == 0 ):
			return -1

		similarityScore = -1

		try:
			if( simMatInput ):
				simMatrix = normalizedTFIDFMatrix
			else:
				simMatrix = DocVect.getSimOrDistMatrix(normalizedTFIDFMatrix)
			
			docMat = np.array(simMatrix)

			row, col = docMat.shape
			if( row != col or row < 2 ):
				return -1

			onesMat = np.ones((row, row))

			#print('\ndocSim Mat:\n', docMat, '\n')

			DocVect.add0sToMainDiag( docMat )
			DocVect.add0sToMainDiag( onesMat )

			#print('\nonesMat:\n', onesMat, '\n')

			docMatNorm = LA.norm( docMat )
			onesMatNorm = LA.norm( onesMat )

			similarityScore = docMatNorm/onesMatNorm
		except:
			genericErrorInfo()

		return similarityScore

	@staticmethod
	def getColEntitySimScore(entyLinks, params=None):

		if( params is None ):
			params = {}

		if( 'sim-coeff' not in params ):
			#params['sim-coeff'] = 0.3
			params['sim-coeff'] = 0.27

		if( 'jaccard-weight' not in params ):
			params['jaccard-weight'] = 0.4

		if( 'overlap-weight' not in params ):
			params['overlap-weight'] = 0.6


		#consider optimizing this because sim matrix is symmetrical j,i can look up i,j
		simMatrix = []

		for i in range(0, len(entyLinks)):
			simMatrix.append( [-1]*len(entyLinks) )
			for j in range(0, len(entyLinks)):

				sim = 0
				if( i == j ):
					sim = 1
				else:
					sim = DocVect.weightedJaccardOverlapSim(
						entyLinks[i], 
						entyLinks[j],
						params['jaccard-weight'],
						params['overlap-weight']
					)
					
					if( sim >= params['sim-coeff'] ):
						sim = 1
					else:
						sim = 0

				simMatrix[i][j] = sim

		return DocVect.getColSimScore(simMatrix, True)



	@staticmethod
	def getEntitySet(ent2dList, tokenizeOnlyTriple=True):
		#tokenizeOnlyTriple is a misnomer, 'MISC' class was added later
		
		clusterSet = set()
		for entTup in ent2dList:
			
			ent, entityClassUpper = entTup
			entityClassUpper = entityClassUpper.upper()

			if( tokenizeOnlyTriple == True and entityClassUpper not in ['PERSON', 'LOCATION', 'ORGANIZATION', 'MISC'] ):
				#don't tokenize datetimes and percent and money
				clusterSet.add( ent.lower() )
			else:
				entityTokens = ent.lower().split(' ')
				for entityTok in entityTokens:
					entityTok = entityTok.strip()
					clusterSet.add( entityTok )

		return clusterSet

	@staticmethod
	def weightedJaccardOverlapSim(firstSet, secondSet, jaccardWeight=0.4, overlapWeight=0.6):
		
		if( jaccardWeight + overlapWeight != 1 ):
			return -1
		
		return (jaccardWeight * jaccardFor2Sets(firstSet, secondSet)) + (overlapWeight * overlapFor2Sets(firstSet, secondSet))


	@staticmethod 
	def getSimOrDistMatrix(matrix, matrixType='sim'):
		
		matrix = np.array(matrix)
		matrix = pairwise_distances(matrix, metric='cosine')

		if( matrixType == 'sim' ):
			matrix = 1 - matrix

		return matrix.tolist()

	@staticmethod
	def tf(term, document):
		return DocVect.freq(term, document)

	@staticmethod
	def freq(term, document):
		return document.split().count(term)

	@staticmethod
	def idf(word, doclist):
		n_samples = len(doclist)
		df = DocVect.numDocsContaining(word, doclist)
		return np.log(n_samples / 1+df)

	@staticmethod
	def l2_normalizer(vec):

		denom = np.sum([el**2 for el in vec])
		
		if( denom <= 0 ):
			return list(vec)

		return [(el / math.sqrt(denom)) for el in vec]

		'''
			print('zero denom')
			print('denom:', denom)
			print('len(vec):', len(vec))
			print('len(retVal):', len(retVal))
			print('retVal[0]', retVal[0])
			print('type(retVal):', type(retVal))
			print('type(vec):', type(list(vec)))
			print('vec:', list(vec))
			print()
			print()
			print()
			return retVal
		'''

	@staticmethod
	def numDocsContaining(word, doclist):
		doccount = 0
		for doc in doclist:
			if DocVect.freq(word, doc) > 0:
				doccount +=1
		return doccount

	@staticmethod
	def buildIDFMatrix(idfVector):
		idf_mat = np.zeros((len(idfVector), len(idfVector)))
		np.fill_diagonal(idf_mat, idfVector)
		return idf_mat

	@staticmethod
	def cosineSim(X, Y):
		try:
			X2Norm = np.linalg.norm(X, 2)
			Y2Norm = np.linalg.norm(Y, 2)
			
			if( X2Norm == 0 or Y2Norm == 0 ):
				return 0

			return round(np.dot(X, Y)/(X2Norm * Y2Norm), 10)
		except:
			genericErrorInfo()
			return 0

	@staticmethod
	def cosineDist(X, Y):
		return 1 - DocVect.cosineSim(X, Y)

	@staticmethod
	def centroidOfMatrix(vectorsList):

		if( len(vectorsList) == 0 ):
			return []	

		centroid = list(np.zeros(len(vectorsList[0])))
		
		for vector in vectorsList:
			for j in range(0, len(vector)):
				centroid[j] += vector[j]

		for i in range(0, len(centroid)):
			centroid[i] = centroid[i]/len(vectorsList)

		return centroid
#directive: googleRetrieveLinksFromPage() consider not relying on tag signature for retrieving links with site directive
#directive: mememetoAggregator single initialization and retrieval from a config file