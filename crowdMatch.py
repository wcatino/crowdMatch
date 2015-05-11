#!/usr/bin/python

from Tkinter import *
import datetime
import functools
from fuzzywuzzy import fuzz
import getpass  # for getting password from user input
import heapq
import itertools
import math
import multiprocessing
import MySQLdb
import random
import re
import sys
import traceback

# global variables here
myPad = 2   # tweak padding of GUI elements for aesthetics

def ScrollListScale(w, h):
    return w,h
    #return int(w * 0.5), int(h)
    #return int(w * 2.0), int(h * 1.5)

def SimilarityFunction_Zero(node0String, node1String):
    return 0

def SimilarityFunction_FuzzTokenSortRatio((node0String, node1String)):
    return fuzz.token_sort_ratio(node0String, node1String)
    
def SimilarityFunction_FuzzTokenSetRatio((node0String, node1String)):
    return fuzz.token_set_ratio(node0String, node1String)
    
def LerpClamp(x, x0, x1, y0, y1):
    x = min(x1, max(x, x0))
    return y0 + (y1 - y0) * (x - x0) / (x1 - x0)
    
def ComputeSimilarityColor(similarity):
    d = LerpClamp(similarity, 0.5, 1, 255, 170)
    color = format(int(d), '02x')
    return '#' + color + 'ff' + color

def RandomColor():
    return '#{:x}{:x}{:x}'.format(random.randint(0, 15), random.randint(0, 15), random.randint(0,15))
    
def MyFrame(master):
# useful for debugging tk's frames and grids
    if True:
        return Frame(master)
    else:
        return Frame(master, bg = RandomColor(), padx = 10, pady = 10)

    
# This class stores a graph structure.
# User input is stored as edges between nodes.
# Edges can be either positive or negative, values can be +1 or -1; 0 means no edge.
# For an edge connecting node n0 and n1 with a value of v, value will be stored in 2 places, both upper and lower triangle of the connectivity matrix:
#     d = {n0: {n1 : v}, n1 : {n0 : v}} 
class CGraph:
    def __init__(self):
        self.g = {}
    
    def Clear(self):
        self.__init__()
    
    def IsNodeIn(self, n):
        return (n in self.g) 
        
    def SortNodes(self, n1, n2):
        if n1 > n2:
            temp = n1
            n1 = n2
            n2 = temp
        return (n1, n2)
        
    def EdgeAdd(self, n1, n2, value):
        if n1 == n2:
            print "ERROR: Nodes cannot connect to self with an edge."
        else:
            if not self.IsNodeIn(n1):
                self.g[n1] = {}
            if not self.IsNodeIn(n2):
                self.g[n2] = {}
            # detect change in existing value
            if False:
                if n2 in self.g[n1]:
                    if self.g[n1][n2] != value:
                        print 'Edge ({0}, {1}) changing value to {2}'.format(n1, n2, value)
            self.g[n1][n2] = value
            self.g[n2][n1] = value

    def EdgeRemove(self, n1, n2):
        bSucceed = False
        if n1 == n2:
            print "ERROR: Nodes cannot connect to self with an edge."
        else:
            if self.IsNodeIn(n1) and self.IsNodeIn(n2):
                if n2 in self.g[n1] and n1 in self.g[n2]:
                    del self.g[n1][n2]
                    if len(self.g[n1]) == 0:
                        del self.g[n1]
                    del self.g[n2][n1]
                    if len(self.g[n2]) == 0:
                        del self.g[n2]
                    bSucceed = True
        if not bSucceed:
            print 'ERROR: EdgeRemove(): Edge not present!!!', n1, n2

    # returns the value of the edge (+1 or -1) or 0 if no edge exists
    def GetEdge(self, n1, n2):
        value = 0
        if self.IsNodeIn(n1):
            if n2 in self.g[n1]:
                value = self.g[n1][n2]
        return value

    # return a list of neighbors of a node
    def GetNeighbors(self, nStart):
        neighbors = []
        if self.IsNodeIn(nStart):
            neighbors.extend(self.g[nStart].keys())
        return neighbors
    
    # return a list of tuples, each corresponding to a neighbor and the edge value
    def GetNeighborsEdges(self, nStart):
        neighbors = []
        if self.IsNodeIn(nStart):
            neighbors.extend(self.g[nStart].items())
        return neighbors
    
    # return a list of nodes that are neighbors connected by a +1 edge
    def GetNeighborsSame(self, nStart):
        neighbors = self.GetNeighborsEdges(nStart)
        return [n[0] for n in neighbors if n[1] == 1]
        
    def GetNumNeighborsSame(self, nStart):
        return len(self.GetNeighborsSame(nStart))
        
    # return True iff a node has at least 1 neighbor
    def HasNeighbors(self, nStart):
        bHasNeighbors = False
        if self.IsNodeIn(nStart):
            if len(self.g[nStart]):
                bHasNeighbors = True
        return bHasNeighbors
        
    # return True iff a node has at least 1 neighbor with an edge value 
    def HasNeighborsValue(self, nStart, value):
        bHasNeighbors = False
        if self.IsNodeIn(nStart):
            for n in self.g[nStart]:
                if self.g[nStart][n] == value:
                    bHasNeighbors = True
                    break
        return bHasNeighbors
        
    def HasNeighborsSame(self, nStart):
        return self.HasNeighborsValue(nStart, 1)
        
    def HasNeighborsDifferent(self, nStart):
        return self.HasNeighborsValue(nStart, -1)

        
    # return a list of lists of nodes - each is a path from node nStart to node nEnd
    # adapted from https://www.python.org/doc/essays/graphs/
    def FindPaths(self, nStart, nEnd, path = None):
        if path is None:
            path = []
        path = path + [nStart]
        if nStart == nEnd:
            return [path]
        if not self.IsNodeIn(nStart) or not self.IsNodeIn(nEnd):
            return []
        paths = []
        for node in self.GetNeighbors(nStart):
            if node not in path:
                newpaths = self.FindPaths(node, nEnd, path)
                for newpath in newpaths:
                    paths.append(newpath)
        return paths

    def PathCountNumberMinusOnes(self, path):
        # returns 0 if all 1 values, implies identity among all the members (and therefore the endpoints)
        # returns 1 if a single -1 value, implies the endpoints are different
        # returns 2 if there are more than one -1 value, implies no relationship between the endpoints
        nMinusOnes = 0
        for i in xrange(len(path) - 1):
            if self.GetEdge(path[i], path[i + 1]) < 0:
                nMinusOnes += 1
                if nMinusOnes > 1:
                    break
        return nMinusOnes
        
    def TestPathsForContradiction(self, paths):
        # a contradiction occurs if the list contains one path of all 1 values, and one path that contains one -1 value
        bContradiction = False
        bSame = False
        bDifferent = False
        for path in paths:
            nMinusOnes = self.PathCountNumberMinusOnes(path)
            print '    nMinusOnes={0},'.format(nMinusOnes), path
            if nMinusOnes == 0:
                bSame = True
            elif nMinusOnes == 1:
                bDifferent = True
            if bSame and bDifferent:
                bContradiction = True
                break
        return bContradiction
    
    # Connect a node to all nodes in a set, with the prescribed edge value
    def NodeToSetConnect(self, n1, set2, value = 1):
        # make sure the node is not in the set
        if n1 in set2:
            print 'WARNING: NodeToSetConnect() node should not be in set!!!!'
        for n2 in set2:
            self.EdgeAdd(n1, n2, value)

    def SetsConnect(self, set1, set2, value = 1):
        for n1 in set1:
            self.NodeToSetConnect(n1, set2, value)
    
    def SetsSetSame(self, set1, set2):
        self.SetsConnect(set1, set2, 1)
    
    def SetsSetDifferent(self, set1, set2):
        self.SetsConnect(set1, set2, -1)
    
    def GetAllConnectedNodes(self, n1, nodes = None):
        if nodes is None:
            nodes = []
        nodes.append(n1)
        neighbors = self.GetNeighbors(n1)        
        for n in neighbors:
            if n not in nodes:
                self.GetAllConnectedNodes(n, nodes)
        return nodes
        
    def GetAllConnectedNodesSame(self, n1, nodes = None):
        if nodes is None:
            nodes = []
        nodes.append(n1)
        neighbors = self.GetNeighborsSame(n1)        
        for n in neighbors:
            if n not in nodes:
                self.GetAllConnectedNodesSame(n, nodes)
        return nodes
        
    def GetNumConnectedNodesSame(self, n1):
        return len(self.GetAllConnectedNodesSame(n1))

    def GetAllConnectedNodesExcludingThis(self, n1, nodes = None):
        connectedNodes = self.GetAllConnectedNodes(n1, nodes)
        # now remove this node - it should appear exactly once
        connectedNodes = [x for x in connectedNodes if x != n1]
        return connectedNodes
        
    # Test
    def Test(self):
        N = 3
        g = self
        print 'N =', N
        for i in range(1, N):
            value = -1# if i < (N / 2) else -1
            g.EdgeAdd(0, i, value)
            g.EdgeAdd(i - 1, i, 1)
        #g.EdgeAdd(N - 2, N - 1, 1)
        # Add a bogus link to see if double negative edges gets ignored properly
        nHuge = 1000000
        g.EdgeAdd(0, nHuge, -1)
        g.EdgeAdd(nHuge, 1, -1)
        
        print g.g
        for i in range(N + 1):
            for j in range(N + 1):
                value = g.GetEdge(i, j)
                if value != 0:
                    print 'edge ({0}, {1}) = {2}'.format(i, j, g.GetEdge(i, j), value)
        for i in range(N + 1):
            print 'neighbors:', i, g.GetNeighbors(i)
            print '    neighbor + edges:', g.GetNeighborsEdges(i)
            print '    neighbors same:', g.GetNeighborsSame(i)


        print 'Find all paths:'
        for i,j in itertools.permutations(range(0, N), 2):
            print '  FindPaths ({0}, {1}):'.format(i, j)
            paths = g.FindPaths(i, j)
            print paths
            print g.TestPathsForContradiction(paths)

        print 'Neighbors of 0:', g.GetNeighbors(0)
        print 'deleting huge node and its neighbors...'
        print g.g
        neighborsOfHuge = g.GetNeighbors(nHuge)
        print 'neighborsOfHuge = ', neighborsOfHuge
        for n in neighborsOfHuge:
            print 'removing edge ({}, {})'.format(nHuge, n)
            g.EdgeRemove(nHuge, n)
            print '.... remaining neighbors = ', g.GetNeighbors(nHuge)
            print '     HasNeighbors({}) = {}'.format(nHuge, g.HasNeighbors(nHuge))
            print g.g
        print 'Neighbors of 0:', g.GetNeighbors(0)
        print 'Neighbors of 1:', g.GetNeighbors(1)
            
        print '#############'
        for i,j in itertools.combinations(range(1, N), 2):
            g.EdgeAdd(i, j, 1)
        for i in range(N + 1):
            neighbors = g.GetNeighbors(i)
            print '_neighbors:', i, neighbors
            for j in neighbors:
                print '      _edge({0},{1})={2}'.format(i,j,g.GetEdge(i,j))

        print 'Find all paths:'
        for i,j in itertools.permutations(range(0, N), 2):
            print '  FindPaths ({0}, {1}):'.format(i, j)
            paths = g.FindPaths(i, j)
            print '{0} paths:'.format(len(paths)), paths
            print g.TestPathsForContradiction(paths)

        ################## start a new graph
        print 'Clear()'
        g.Clear()
        print g.g
        
        N = 3
        set0 = set()
        set1 = set()
        for n in range(N):  
            print 'n = ', n
            if len(set0) > 0:
                g.NodeToSetConnect(n, set0)
            set0.add(n)
            print g.g
            
            nn = 100 + n
            print 'nn = ', nn
            if len(set1) > 0:
                g.NodeToSetConnect(nn, set1)
            set1.add(nn)
            print g.g
            
        for n in set0 | set1:
            print '     HasNeighbors({}) = {}'.format(n, g.HasNeighbors(n))
            print '    neighbors of {}:'.format(n), g.GetNeighbors(n)
            theNodes = g.GetAllConnectedNodes(n)
            print '_____all nodes connected to {}:'.format(n), theNodes
            print '_ _ _all nodes connected to {}, excluding this:'.format(n), g.GetAllConnectedNodesExcludingThis(n)
            

        print 'Join set0 and set1...'
        g.SetsSetSame(set0, set1)
        for n in set0 | set1:
            nodes = g.GetAllConnectedNodes(n)
            print '>>> all nodes connected to {}:'.format(n), nodes

        # clear the graph so that we can do some real work
        print 'Clear()'
        g.Clear()


class CDb:

    def __init__(self, username, password):
        self.userName = username
        self.password = password
        self.hostName = 'klab.c3se0dtaabmj.us-west-2.rds.amazonaws.com'
        self.dbName = 'vote0'
        self.table = 'vote0'
        self.tableData = 'data1'
        # create a connection to the database
        self.con = MySQLdb.connect(
                    user = username, 
                    passwd = password, 
                    host = self.hostName, 
                    db = self.dbName,
                    charset='utf8',
                    use_unicode=True)  # essential for proper handling of unicode characters
    
        # create a Cursor object to execute queries
        self.cur = self.con.cursor()
        
    # INSERT one VALUE at a time (slow!)
    def Vote(self, id0, id1, bSame, iClick):
        # schema:  date, user, id0, id1, bMatch, click
        cmd = 'INSERT INTO {0} VALUES ("{1}", "{2}", {3}, {4}, {5}, {6})'.format(
            self.table,
            datetime.datetime.now().isoformat(),
            self.userName,
            id0,
            id1,
            '1' if bSame else '0',
            iClick)
        self.cur.execute(cmd)
        self.con.commit()

    # INSERT all the VALUES at once (fast!)
    def VoteBegin(self, iSame, iClick):
        self.bFirstVote = True
        self.iSame = iSame
        self.iClick = iClick
        self.cmdList = ['INSERT INTO {0} VALUES '.format(self.table)]
        
    def VoteAdd(self, id0, id1):
        if not self.bFirstVote:
            self.cmdList.append(', ')
        self.bFirstVote = False
        #self.cmdList.append('("{0}", "{1}", {2}, {3}, {4}, {5})'.format(
        self.cmdList.append('(NOW(), "{1}", {2}, {3}, {4}, {5})'.format(
            datetime.datetime.now().isoformat(),
            self.userName,
            id0,
            id1,
            self.iSame,
            self.iClick))
    
    def VoteEnd(self):
        if not self.bFirstVote:
            cmd = ''.join(self.cmdList)
            #print 'cmd = ', cmd
            self.cur.execute(cmd)
            self.con.commit()

    def DownloadList(self):
        #cmd = 'SELECT d, freq FROM {0} LIMIT 1000'.format(self.tableData)
        cmd = 'SELECT d, freq FROM {0}'.format(self.tableData)
        self.cur.execute(cmd)
        dataList = [{'data' : x[0].strip(' \t\n"'), 'freq' : x[1]} for x in self.cur.fetchall()]
        print '%d records loaded.' % len(dataList)
        #print dataList[:10]
        return dataList
        
    def DownloadRelations(self):
        #cmd = 'SELECT d, freq FROM {0} LIMIT 1000'.format(self.tableData)
        print 'Downloading relations...'
        cmd = 'SELECT id0, id1, bMatch freq FROM {0};'.format(self.table)
        self.cur.execute(cmd)
        relations = self.cur.fetchall()
        print '%d relations loaded.' % len(relations)
        return relations
        
class CListFiltered:

    def __init__(self, listFull, graph):
        self.listFull = listFull
        self.lenFull = len(listFull)
        self.listIndexFiltered = range(self.lenFull)
        self.lenFiltered = self.lenFull
        self.graph = graph
    
    def LengthFiltered(self):
        return self.lenFiltered
        
    def LastIndexFiltered(self):
        return self.lenFiltered - 1
    
    def GetFilteredListOfStrings(self):
        return [self.listFull[i]['data'] for i in self.listIndexFiltered]

    def GetStringFromFullIndex(self, i):
        return self.listFull[i]['data']
        
    def GetFullIndexFromFilteredListIndex(self, iFiltered):
        return self.listIndexFiltered[iFiltered]

    def SortIndexFilteredByGroupSize(self, bSortByGroupSize = False):
        if bSortByGroupSize:
            list0 = [(i, self.graph.GetNumNeighborsSame(i)) for i in self.listIndexFiltered]
            list0.sort(key = lambda x: x[1], reverse = True)
            self.listIndexFiltered = [x[0] for x in list0]
        
    def FilterApply(self, filterString, filterWords, bCaseSensitive = False, bSortByGroupSize = False):
        if len(filterString) > 0:
            flags = 0
            if bCaseSensitive:
                s = filterString
                self.listIndexFiltered = [i for i in xrange(self.lenFull) if (s in self.listFull[i]['data'])]
            else:
                s = filterString.lower()
                self.listIndexFiltered = [i for i in xrange(self.lenFull) if (s in self.listFull[i]['data'].lower())]
        else:
            self.listIndexFiltered = range(self.lenFull)
            
        for word in filterWords:
            s = word.lower()
            self.listIndexFiltered = [i for i in self.listIndexFiltered if (s in self.listFull[i]['data'].lower())]
            
        self.SortIndexFilteredByGroupSize(bSortByGroupSize)
        
        self.lenFiltered = len(self.listIndexFiltered)
        if False:
            print 'filterString = ', filterString
            print 'GetFilteredListOfStrings() = ', self.GetFilteredListOfStrings()
            print 'lenFiltered = ', self.lenFiltered
            print 'listIndexFiltered = ', self.listIndexFiltered

class CScrollList:
    def __init__(self, master, data, gridx, gridy, selMode = BROWSE, height = None, width = None):
        h = height if height is not None else 20
        w = width  if width  is not None else 50

        self.frame = MyFrame(master)
        self.lb = self.Create(self.frame, data, 0, 0, selMode, height = h, width = w)
        self.frame.grid(column = gridx, row = gridy)
        self.DataSet(data)
        
    def DataSet(self, d):
        self.data = d
        lb = self.lb

        #print '---------------- DataSet()  :', d
        lb.delete(0, END)
        for datum in d:
            lb.insert(END, datum['text'])
        self.SetSingleSelection(0)
        
    def DataGet(self):
        return self.data
        
    def Create(self, frame, listContents, gridx, gridy, selMode = BROWSE, height = None, width = None):
        width, height = ScrollListScale(width, height)
        sb = Scrollbar(frame, orient = VERTICAL)
        sb2 = Scrollbar(frame, orient = HORIZONTAL)
        lb = Listbox(frame, yscrollcommand = sb.set, xscrollcommand = sb2.set, selectmode = selMode,
            selectbackground = '#ffff00', selectforeground = '#000',
            disabledforeground = '#ff0000', exportselection = 0, height = height, width = width)
        sb.config(command = lb.yview)
        sb2.config(command = lb.xview)
        
        lb.grid(row = 0, column = 0, sticky = N + S + E + W, padx = myPad, pady = myPad)
        sb.grid(row = 0, column = 1, sticky = N + S)
        sb2.grid(row = 1, column = 0, sticky = E + W)
        
        return lb

    def SetSingleSelection(self, newSelection = None):
        lb = self.lb
        lb.selection_clear(0, lb.size() - 1)
        if newSelection != None:
            lb.selection_set(newSelection)
            lb.activate(newSelection)
            lb.see(newSelection)
        else:
            lb.see(0)
        lb.xview(0)     # scroll to the left (column 0)
        
    def GetSelectedNodes(self):
        # returns the list of nodes that correspond to the current selection of this box
        return [self.data[int(i)]['node'] for i in self.lb.curselection()]
        
class CScrollListPair:
    def __init__(self, app, master, data, gridx, gridy, similarityFunction, selMode = BROWSE, height = None, width = None, width2 = None):
        h = height if height is not None else 15
        w0 = width  if width  is not None else 40
        w1 = width2 if width2 is not None else (w0 * 1 / 2)
        
        self.app = app
        self.frame = MyFrame(master)
        self.similarityFunction = similarityFunction
        sl0 = CScrollList(self.frame, data, gridx = 0, gridy = 0, selMode = selMode, height = h, width = w0)
        sl1 = CScrollList(self.frame, data, gridx = 1, gridy = 0, selMode = BROWSE, height = h, width = w1)
        sl1.lb.config(bg='#f5f5f5')
        self.sl = [sl0, sl1]
        self.frame.grid(column = gridx, row = gridy)

    def DataSet(self, d):
        self.sl[0].DataSet(d)
        
    def UpdateSameNodeList(self):
        # update the right-hand list to show all elements that are the same as the selection(s) in the left-hand list
        sameNodes = set()
        for node in self.sl[0].GetSelectedNodes():
            # set the list to the members of the set
            print 'UpdateSameNodeList() node = ', node
            sameNodes |= set(self.app.graph.GetNeighborsSame(node))
        self.sl[1].DataSet([{'node' : n, 'text': self.app.listFiltered.GetStringFromFullIndex(n)} for n in sorted(sameNodes)])
        self.sl[1].SetSingleSelection(None)


class CApp:
        
    def __init__(self, master, db, graph):
        self.db = db
        self.master = master
        self.master.title("crowdMatch v0.1")
        self.graph = graph
        self.scrollListPairs = []
        self.nodeSelected = 0       # the index (node number) of the current selection of the top window, against which all other lists are compared via similarity functions

        random.seed()
        self.clickCount = 0
        self.prevVote = (0,0,0)
        
        self.frame = MyFrame(master)
        self.frame.grid(sticky = N + S + E + W)

        frameLeft = MyFrame(self.frame)
        frameLeft.grid(row = 0, column = 0, sticky = N + S + W, rowspan = 3, padx = 1)
        
        # right frame
        frame = MyFrame(self.frame)
        frame.grid(row = 0, column = 1, sticky = N + S + E, padx = 1)

        # children of the right frame
        frameTopList = MyFrame(frame)
        frameTopList.grid(row = 0, column = 0, sticky = N + E + W, padx = 1)
        
        frameBetweenLists = MyFrame(frame)
        frameBetweenLists.grid(row = 1, column = 0, sticky = E + W, padx = 5, pady = 5)

        frameLists = MyFrame(frame)
        frameLists.grid(row = 2, column = 0, sticky = E + W, padx = 5, pady = 5)
        
        frameBottom = MyFrame(frame)
        frameBottom.grid(row = 3, column = 0, sticky = S + E + W, padx = 5, pady = 5)

        # frameTopList
        curRow = 0
        self.labelTitle = Label(frameTopList, text = ' ')#'crowdMatch')
        self.labelTitle.grid(row = curRow, column = 0, sticky = N + E + W, padx = myPad, pady = myPad)

        curRow += 1

        self.listFiltered = CListFiltered(self.db.DownloadList(), self.graph)
        
        self.slp0 = CScrollListPair(self, frameTopList, [], 0, curRow, SimilarityFunction_Zero, selMode = BROWSE, height = 15, width = 60, width2 = 60)
        self.scrollListPairs.append(self.slp0)
        self.lb0 = self.slp0.sl[0].lb
        self.lb0b = self.slp0.sl[1].lb
        self.lb0b.config(selectmode = EXTENDED)
        self.lb0.bind('<<ListboxSelect>>', self.OnLb0Select)
            
        self.bTopDiffIndividual = Button(frameTopList, text="Different\n(Individuals)", command = self.ClickedDifferentIndividuals, bg = '#ff9999', activebackground = '#ff0000')
        self.bTopDiffIndividual.grid(row = curRow, column = 1, sticky = 'new', padx = myPad, pady = myPad + 10, ipady = 30)

        self.bTopDiffGroup = Button(frameTopList, text="Different\n(2 Groups)", command = self.ClickedDifferentGroup, bg = '#ff9999', activebackground = '#ff0000')
        self.bTopDiffGroup.grid(row = curRow, column = 1, sticky = 'sew', padx = myPad, pady = myPad + 10, ipady = 30)

        curRow += 1

        # frameBetweenLists
        curRow = 0    
        self.bSame = Button(frameBetweenLists, text="Same", command = self.ClickedSame, bg = '#99ff99', activebackground = '#00ff00')
        #self.bSame.grid(row = curRow, column = 0, sticky = W, padx = myPad, pady = myPad)
        self.bSame.grid(row = curRow, column = 0, sticky = N + S + W, padx = myPad + 30, pady = myPad, ipadx = 40)
        
        self.bDiff = Button(frameBetweenLists, text="Different", command = self.ClickedDifferent, bg = '#ff9999', activebackground = '#ff0000')
        #self.bDiff.grid(row = curRow, column = 0, sticky = E, padx = myPad, pady = myPad)
        self.bDiff.grid(row = curRow, column = 2, sticky = N + S + E, padx = myPad + 30, pady = myPad, ipadx = 40)
        curRow += 1
                
        # frameLists
        curRow = 0    
        self.scrollListPairs.append(CScrollListPair(self, frameLists, [], 0, 0, SimilarityFunction_FuzzTokenSetRatio,  selMode = EXTENDED))
        self.scrollListPairs.append(CScrollListPair(self, frameLists, [], 1, 0, SimilarityFunction_FuzzTokenSortRatio, selMode = EXTENDED))
        #self.scrollListPairs.append(CScrollListPair(self, frameLists, [], 2, 0, SimilarityFunction_Zero, selMode = EXTENDED))

        for i, slp in enumerate(self.scrollListPairs):
            slp.sl[1].lb.bind('<Double-Button-1>', functools.partial(self.OnDoubleClicked, iSlp = i, iSl = 1))
            if i > 0:
                slp.sl[0].lb.bind('<<ListboxSelect>>', self.SimilarListsRightUpdate)
                slp.sl[0].lb.bind('<Double-Button-1>', functools.partial(self.OnDoubleClicked, iSlp = i, iSl = 0))
        
        curRow += 1
        

        '''
        self.bRand = Button(frame, text = "Random", command = self.ClickedRandom, bg = '#7799ff', activebackground = '#0000ff')
        self.bRand.grid(row = 3, column = 4, sticky = N + S + E + W, padx = myPad, pady = myPad)
        
        # 
        self.bMirror0 = Button(frame, text = "Jump", command = functools.partial(self.ClickedMirror, 0), bg = '#aaaaff', activebackground = '#0000ff')
        self.bMirror0.grid(row = 1, column = 4, sticky = S + E + W, padx = myPad, pady = myPad)
        
        self.bMirror1 = Button(frame, text = "Jump", command = functools.partial(self.ClickedMirror, 1), bg = '#aaaaff', activebackground = '#0000ff')
        self.bMirror1.grid(row = 4, column = 4, sticky = N + E + W, padx = myPad, pady = myPad + 12)
        '''
        
        # frameBottom
        curRow = 0
        self.button = Button(frameBottom, text = "QUIT", command = frame.quit, bg = '#aaaaaa', activebackground = '#ddddff')
        self.button.grid(row = curRow, padx = myPad, pady = myPad, ipadx = 20, ipady = 5)
        curRow += 1
             
        # frameLeft widgets
        curRow = 0
        FILTER_ENTRY_WIDTH = 30
        self.labelBlankTitle = Label(frameLeft, text = ' ')
        self.labelBlankTitle.grid(row = curRow, column = 0, sticky = N + S + W, padx = myPad, pady = 0)
        curRow += 1

        self.labelFilter = Label(frameLeft, text = 'Filter:')
        self.labelFilter.grid(row = curRow, column = 0, sticky = N + S + W, padx = myPad, pady = 0)
        curRow += 1
        
        self.entryFilter = Entry(frameLeft, width = FILTER_ENTRY_WIDTH)
        self.entryFilter.grid(row = curRow, column = 0, sticky = N + E + W, padx = myPad)
        curRow += 1

        self.bFilterClear = Button(frameLeft, text = "X", command = self.ClickedFilterClear)
        self.bFilterClear.grid(row = curRow, column = 0, sticky = N + S + E)
        curRow += 1

        self.caseSensitive = IntVar()
        self.caseSensitive.set(0)
        self.checkboxCaseSensitive = Checkbutton(frameLeft, text = "Case sensitive", variable = self.caseSensitive, \
                 onvalue = 1, offvalue = 0, height=1, \
                 width = 20)
        self.checkboxCaseSensitive.grid(row = curRow, column = 0, sticky = W, padx = myPad)
        curRow += 1

        self.slWordFilters = CScrollList(frameLeft, [], 0, curRow, width = FILTER_ENTRY_WIDTH, height = 20, selMode = MULTIPLE)
        self.lbWordFilters = self.slWordFilters.lb
        self.lbWordFilters.config(selectbackground = '#ffff00', disabledforeground = '#ff0000', exportselection=0)
        curRow += 1
        
        self.bFilterClear = Button(frameLeft, text = "X", command = self.ClickedWordFilterClear)
        self.bFilterClear.grid(row = curRow, column = 0, sticky = N + S + E)
        curRow += 1

        
        self.bSortByGroupSize = IntVar()
        self.bSortByGroupSize.set(1)
        self.sortByGroupSize = Checkbutton(frameLeft, text = "Sort by Cluster Size", variable = self.bSortByGroupSize, \
                 onvalue = 1, offvalue = 0, height=1, \
                 width = 20)
        self.sortByGroupSize.grid(row = curRow, column = 0, sticky = W, padx = myPad)
        curRow += 1


        self.bFilterApply = Button(frameLeft, text = "Apply", command = self.ClickedFilterApply, bg = '#7799ff', activebackground = '#0000ff')
        self.bFilterApply.grid(row = curRow, column = 0, sticky = N + S + E + W, padx = myPad, pady = myPad)
        curRow += 1

        self.labelLength = Label(frameLeft, justify = RIGHT)
        self.LabelLengthUpdate()
        self.labelLength.grid(row = curRow, column = 0, sticky = S + E, padx = myPad)
        curRow += 1
                
        self.ListsUpdate()
        
        if True:    # make all grid rows and columns have weight 1
            self.RecurseAddWeight(self.master)

    def RecurseAddWeight(self, w):
        #print 'w = ', w,
        nCols, nRows = w.grid_size()

        if True:
            theWeight = 1
        else:
            if w.winfo_class() == 'Listbox':
                theWeight = 2
            else:
                theWeight = 1

        if nCols >= 0 and nRows >= 0:
            for iRow in xrange(nRows):
                w.rowconfigure(iRow, weight = theWeight)
            for iCol in xrange(nCols):
                w.columnconfigure(iCol, weight = theWeight)
            
        #print '  ({} x {})'.format(nCols, nRows),  w.winfo_class()
        for ww in w.grid_slaves():           #winfo_children():
            self.RecurseAddWeight(ww)
        
        
    def CursorSetBusy(self, bBusy = True):
        if bBusy:
            self.master.config(cursor = "watch")
        else:
            self.master.config(cursor = "")
        self.master.update()

    def ListsUpdate(self):
        self.listFiltered.SortIndexFilteredByGroupSize(self.bSortByGroupSize.get())

        list0 = [{'node' : i, 'text': ('%3d ' % self.graph.GetNumNeighborsSame(i)) + self.listFiltered.GetStringFromFullIndex(i)} for i in self.listFiltered.listIndexFiltered]
            
        self.slp0.sl[0].DataSet(list0)
        self.slp0.sl[0].SetSingleSelection(0)

        self.LabelLengthUpdate()
        self.OnLb0Select(None, bUpdateSimilarLists = False)
        
    def SimilarListsLeftUpdate(self):
        #traceback.print_stack()
        LIST_LEN = 400
        nodeSelectedString = self.listFiltered.GetStringFromFullIndex(self.nodeSelected)
        for slp in self.scrollListPairs[1:]:
            # update the left hand list
            if False:   # single-processor version
                leftList = []
                simFunc = slp.similarityFunction
                for n in self.listFiltered.listIndexFiltered:
                    if n not in self.nodeSelectedSameNodes:
                        similarity = simFunc(self.listFiltered.GetStringFromFullIndex(n), nodeSelectedString)
                        leftList.append((n, similarity))
            else:   # parallel version
                p = multiprocessing.Pool()
                nodeList = [n for n in self.listFiltered.listIndexFiltered if n not in self.nodeSelectedSameNodes]
                similarities = p.map(slp.similarityFunction, [(nodeSelectedString, self.listFiltered.GetStringFromFullIndex(n)) for n in nodeList])
                leftList = zip(nodeList, similarities)
                
            leftList = heapq.nlargest(LIST_LEN, leftList, key = lambda x : x[1])
            leftList = [{'node' : x[0], 'similarity' : x[1], 'text' : '%5.2f %s' % (x[1], self.listFiltered.GetStringFromFullIndex(x[0]))} for x in leftList]
            slp.sl[0].DataSet(leftList)
            lb = slp.sl[0].lb
            for i in xrange(len(leftList)):
                if self.graph.GetEdge(self.nodeSelected, leftList[i]['node']) == -1:
                    lb.itemconfig(i, bg = '#f99')
                else:
                    lb.itemconfig(i, bg = ComputeSimilarityColor(leftList[i]['similarity']))
            
            slp.sl[0].SetSingleSelection(None)     # scroll to top of list, none selected

            # update the right-hand list to show all elements that are the same as the selection(s) in the left-hand list
            slp.UpdateSameNodeList()
            
    def SimilarListsRightUpdate(self, event):
        for slp in self.scrollListPairs[1:]:
            nodes = slp.sl[0].GetSelectedNodes()
            setNodesSame = set()
            for node in nodes:
                setNodesSame.add(node)
                for n in self.graph.GetNeighborsSame(node):
                    setNodesSame.add(n)
            nodeList = sorted(list(setNodesSame))
            slp.sl[1].DataSet([{'node':n, 'text': self.listFiltered.GetStringFromFullIndex(n)} for n in nodeList])

    def UpdateWordList(self):
        sl = self.slWordFilters
        strSelection = self.listFiltered.GetStringFromFullIndex(self.nodeSelected)
        listWords = strSelection.split()
        
        if True: # This breaks the unicode encodings, but we'll add these to the existing list
            str2 = re.sub('[\W_]', ' ', strSelection, re.UNICODE)       # get rid of all non-letters
            str2 = re.sub('(\D)(\d)', r'\1 \2', str2, re.UNICODE)       # insert spaces between transitions between letters and numbers
            str2 = re.sub('(\d)(\D)', r'\1 \2', str2, re.UNICODE)       # insert spaces between transitions between letters and numbers
            set0 = set(listWords)
            l2 = [x for x in str2.split() if x not in set0 and len(x) > 1]
            set0 = set0 | set(l2)
            listWords = sorted(list(set0))
            
        #listWords = [x for x in listWords if len(x) > 1]   # weed out single letters
        self.numWordFilters = len(listWords)
        self.slWordFilters.DataSet([{'text':s} for s in listWords])
        self.slWordFilters.SetSingleSelection(None)        # scroll to top of list

    def OnLb0Select(self, eventObject, bUpdateSimilarLists = True):
        #print 'OnLb0Select(): event = ', eventObject
        self.CursorSetBusy(True)
        selections = self.lb0.curselection()
        if len(selections):
            iSelectionFiltered = int(self.lb0.curselection()[0])
            self.nodeSelected = self.listFiltered.GetFullIndexFromFilteredListIndex(iSelectionFiltered)
            self.nodeSelectedSameNodes = self.graph.GetNeighborsSame(self.nodeSelected)
            self.nodeSelectedSameNodes.append(self.nodeSelected)
            self.nodeSelectedSameNodes.sort()
        else:
            self.nodeSelected = 0
            self.nodeSelectedSameNodes = []
        #print 'OnLb0Select: iSelectionFiltered = ', iSelectionFiltered, ', nodeSelected = ', self.nodeSelected

        self.UpdateWordList()
        
        # set the list to the members of the set
        sameNodes = self.nodeSelectedSameNodes
        self.slp0.sl[1].DataSet([{'node':n, 'text':'%5d %s' % (self.listFiltered.listFull[n]['freq'], self.listFiltered.GetStringFromFullIndex(n))} for n in sameNodes])
        self.slp0.sl[1].SetSingleSelection(None)
        if bUpdateSimilarLists:
            self.SimilarListsLeftUpdate()
        self.CursorSetBusy(False)
        
    def LabelLengthUpdate(self):
        nEntries = self.listFiltered.LengthFiltered()
        if nEntries == 1:
            descriptor = 'entry'
        else:
            descriptor = 'entries'
        self.labelLength.config(text = '({0} {1})'.format(nEntries, descriptor))
        
    def ClickedFilterApply(self):
        self.RestoreSelection_Set()
        filterString = self.entryFilter.get()
        filterWords = [self.lbWordFilters.get(iWord) for iWord in self.lbWordFilters.curselection()]
        self.listFiltered.FilterApply(filterString, filterWords, self.caseSensitive.get(), self.bSortByGroupSize.get())
        self.ListsUpdate()
        self.slp0.sl[0].SetSingleSelection(0)
        self.RestoreSelection_Update()

    def ClickedFilterClear(self):
        self.entryFilter.delete(0, END)

    def ClickedWordFilterClear(self):
        listSize = self.lbWordFilters.size()
        if listSize > 0:
            self.lbWordFilters.selection_clear(0, listSize - 1)
        
    def ClickedSameOrDifferent(self, bSame, diffSubset = None):
        print 'bSame=',bSame,'diffSubset=',diffSubset
        if bSame:
            strSameOrDiff = 'Same'
            iSame = 1
            edgeValue = 1
        else:
            strSameOrDiff = 'Different'
            iSame = 0
            edgeValue = -1

        bClickInc = False

        i0 = self.RestoreSelection_Set()
        
        self.db.VoteBegin(iSame, self.clickCount)
                       
        set0 = set([i0])
        set0.update(set(self.graph.GetNeighborsSame(i0)))
        
        if diffSubset == None:      
            # diff with the bottom lists
            set1Selections = []
            set1 = set([])
            print 'set1 empty:', set1
            for slp in self.scrollListPairs[1:]:
                set1Selections.extend(slp.sl[0].GetSelectedNodes())
            print 'set1Selections: ', set1Selections
            for n1 in set1Selections:
                set1.add(n1)
                for n in self.graph.GetNeighborsSame(n1):
                    set1.add(n)
        else:
            set1Selections = self.slp0.sl[1].GetSelectedNodes()
            set1 = set(set1Selections)
            print 'set1Selections:', set1Selections, 'set1:', set1

        if bSame:
            # if an element exists in both, for same, keep it in set0 - we don't need to link it to others in set0
            set1 -= set0
        else:
            # if there is no intersection between set0 and set1, create different edges between all of set1
            if not set0.isdisjoint(set1):
                set1 = set1Selections
                print 'overlap.... so set1 = just selections: '
            # if an element exists in both, for different, move it to set1 to make it different from the other elements of set0
            set0 = [x for x in set0 if x not in set1]
                
        print ' set0:', set0
        print ' set1:', set1
        
        pairs = [(i0,i1) for i0 in set0 for i1 in set1]
        print '  pairs0:', pairs
        if bSame or diffSubset == 'individuals':   # only for same or individualsSubset do we connect all elements of set1 to each other
            pairs.extend(itertools.combinations(set1, 2))
            print '  pairs1:', pairs
        for idx0, idx1 in pairs:
            print "%3d.  %d and %d are %s" % (self.clickCount, idx0, idx1, strSameOrDiff)
            self.db.VoteAdd(idx0, idx1)
            self.graph.EdgeAdd(idx0, idx1, edgeValue)
            bClickInc = True

        if bClickInc:
            self.db.VoteEnd()
            self.clickCount += 1
        self.ListsUpdate()
        self.RestoreSelection_Update()
        
    def RestoreSelection_Set(self, node = None):
        if node == None:
            sl00 = self.scrollListPairs[0].sl[0]
            nodes = sl00.GetSelectedNodes()
            self.nodeToRestore = nodes[0] if len(nodes) else 0
        else:
            self.nodeToRestore = node
        return self.nodeToRestore

    def RestoreSelection_Update(self):
        nodeToReturnTo = self.nodeToRestore
        bFound = False
        if nodeToReturnTo != None:
            sl00 = self.scrollListPairs[0].sl[0]
            d = sl00.DataGet()
            # go to node we last one selected
            for iDatum, datum in enumerate(d):
                if datum['node'] == nodeToReturnTo:
                    bFound = True
                    sl00.SetSingleSelection(iDatum)
                    break
            if not bFound:
                # if it is no longer in the list, go to 1st node that is the same as the last one selected
                sameNodes = self.graph.GetNeighborsSame(nodeToReturnTo)
                if len(sameNodes) > 1:
                    for iDatum, datum in enumerate(d):
                        if datum['node'] in sameNodes:
                            bFound = True
                            sl00.SetSingleSelection(iDatum)
                            break
        if bFound:
            self.OnLb0Select(None)

    def OnDoubleClicked(self, event, iSlp, iSl):
        self.RestoreSelection_Set(self.scrollListPairs[iSlp].sl[iSl].GetSelectedNodes()[0])
        self.RestoreSelection_Update()
        
    def ClickedDifferentIndividuals(self):
        self.ClickedSameOrDifferent(False, diffSubset = 'individuals')
    
    def ClickedDifferentGroup(self):
        self.ClickedSameOrDifferent(False, diffSubset = 'group')
                        
    def ClickedSame(self):
        self.ClickedSameOrDifferent(True)

    def ClickedDifferent(self):
        self.ClickedSameOrDifferent(False)
        
    def ClickedRandom(self):
        newSelection = random.randint(0, self.listFiltered.LastIndexFiltered())
        self.sl0.SetSingleSelection(newSelection)
        self.sl1.SetSingleSelection(newSelection)

    # iListBox is the index of the box adjacent to the button, 0=top, 1=bottom
    def ClickedMirror(self, iListBox):
        if iListBox == 0:
            self.sl0.SetSingleSelection(self.sl1.lb.curselection()[0])
        else:
            self.sl1.SetSingleSelection(self.sl0.lb.curselection()[0])

            
##########################################################################################      
if __name__ == "__main__":
    print datetime.datetime.now().isoformat()
    username = raw_input('Please enter your username: ')
    password = getpass.getpass('Enter password for database: ')
    print 'Connecting to database...'
    
    graph = CGraph()
    #graph.Test()

    db = CDb(username, password)
    
    if True:
        relations = db.DownloadRelations()
        for r in relations:
            graph.EdgeAdd(r[0], r[1], 1 if r[2] == 1 else -1)
        print 'Relations loaded.'
    
    root = Tk()
    app = CApp(root, db, graph)
    root.mainloop()
    root.destroy() # optional; see description below
