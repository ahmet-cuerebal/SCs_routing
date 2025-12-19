import sys
import time
import pandas as pd
from numpy import number
from numpy.lib.user_array import container

import random
import copy


class Location:
    def __init__(self, x, y):
        self.x = x
        self.y = y

    def distance(self, location):
        return abs(self.x - location.x) + abs(self.y - location.y)

    def __str__(self):
        return "(" + str(self.x) + "," + str(self.y) + ")"


class Crane:
    def __init__(self, name, kind, location, list_of_containers, buffer, Jbc=None):
        if Jbc is None:
            Jbc = []
        self.name = name
        self.kind = kind
        self.location = location
        self.list_of_containers = list_of_containers
        self.buffer = buffer
        self.Jbc = Jbc # the list of containers in the buffer at start
        self.avl = 0

    def __str__(self):
        return "Crane" + self.name

class Container:
    UNSET_TIME = -1
    NO_SC = -1

    def __init__(
        self,
        index,
        name,
        kind,                 # "U" / "L" / "R"
        crane,
        start_position,
        end_position,
        is_job=True,
        start_time=None,
        end_time=None,
        container_above=None,
        container_under=None,
    ):
        self.index = index
        self.name = name
        self.kind = kind
        self.crane = crane

        self.start_position = start_position
        self.end_position = end_position
        self.current_position = start_position

        self.is_job = is_job
        # always define attributes:
        self.start_time = start_time if is_job else None
        self.end_time = end_time if is_job else None

        self.container_above = container_above
        self.container_under = container_under
        self.time_when_container_above_moved = -1

        self.is_in_buffer = False
        self.buffer_enter_time = None
        self.buffer_exit_time = None

        self.sc_index = None
        self.is_calculated = False
        self.is_onShip = False

    def __eq__(self, other):
        return isinstance(other, Container) and self.index == other.index

    def __hash__(self):
        return hash(self.index)

    def __str__(self):
        return self.name + "" + self.kind


class SC:
    def __init__(self, name, start_position, index):
        self.name = name
        self.start_position = start_position
        self.current_position = start_position
        self.last_position = start_position
        self.last_job_finish_time = 0
        self.next_job = None
        self.last_job = None
        self.avl = 0
        self.index = index

    def __str__(self):
        return self.name


class Buffer:
    def __init__(self, capacity, number_of_containers=0):
        self.capacity = capacity
        self.number_of_containers = number_of_containers

    def __str__(self):
        return "Buffer: " + str(self.capacity)


class MSCRBProblem:
    tq, tv, ts, tb, pv, M, arj= 80, 20, 5, 5, 1, 10000, 0

    def __init__(self, containers=None, containers_sorted=None, scs=None, cranes=None, bc=4, nv=0, nq=0, R=0,
                 Tunloaded=None, tjob=None):
        self.containers = [] if containers is None else containers
        self.containers_sorted = [] if containers_sorted is None else containers_sorted
        self.scs = [] if scs is None else scs
        self.cranes = [] if cranes is None else cranes
        self.bc = bc  # capacity of the buffer of crane (4 containers)
        self.nv = nv  # the number of SCs
        self.nq = nq  # the number of cranes (quay cranes)
        self.R = R  # restacking set
        self.Tunloaded = {} if Tunloaded is None else Tunloaded
        self.tjob = {} if tjob is None else tjob
        self.A = None

    def read_from_file(self, filename, compute_times=True):
        f = open(filename, "r")
        self.bc = int(f.readline())
        self.nq = int(f.readline())
        nl = 0  # number of loading cranes
        nu = 0  # number of unloading cranes
        self.cranes = []
        for i in range(1, self.nq + 1):
            splittedLine = f.readline().split()
            name = splittedLine[0]
            [x, y] = map(int, splittedLine[1:])
            self.cranes.append(Crane(name, name[0], Location(x, y), [], Buffer(self.bc), []))
            if name[0] == "U":
                nu = nu + 1
            else:
                nl = nl + 1
        self.nv = int(f.readline())
        self.scs = []
        for i in range(1, self.nv + 1):
            [x, y] = map(int, f.readline().split())
            self.scs.append(SC("SC" + str(i), Location(x, y), index = i-1))

        totalNumberOfContainers = 0
        numC = 0

        for i in range(1, self.nq + 1):
            splittedLine = f.readline().split()
            craneName = splittedLine[1]
            craneNumber = int(craneName[1])
            currentCrane = self.cranes[craneNumber - 1]
            Jbc_number = int(splittedLine[0])
            totalNumberOfContainers += Jbc_number
            if craneName[0] == "U":
                for k in range(0, Jbc_number):
                    [x1, y1, x2, y2] = map(int, f.readline().split())
                    numC += 1
                    c = Container(numC -1, "C" + str(numC), "U", currentCrane, Location(x1, y1), Location(x2, y2))
                    c.is_in_buffer = True
                    currentCrane.list_of_containers.append(c)
                    currentCrane.Jbc.append(c)
                    self.containers.append(c)
            else:
                for k in range(0, Jbc_number):
                    numC += 1
                    c = Container(numC -1, "C" + str(numC), "L", currentCrane, None, None,
                                  False)
                    c.is_in_buffer = True
                    currentCrane.list_of_containers.append(c)
                    currentCrane.Jbc.append(c)
                    self.containers.append(c)

            splittedLine = f.readline().split()
            numberOfContainers = int(splittedLine[0])
            totalNumberOfContainers += numberOfContainers
            craneName = splittedLine[1]
            craneNumber = int(craneName[1])
            currentCrane = self.cranes[craneNumber - 1]
            for j in range(0, numberOfContainers):
                [x1, y1, x2, y2] = map(int, f.readline().split())
                numC += 1
                c = Container(numC -1, "C" + str(numC), craneName[0], currentCrane, Location(x1, y1), Location(x2, y2))

                currentCrane.list_of_containers.append(c)
                self.containers.append(c)

        maxNumOfContainers = 0
        for i in range(1, self.nq + 1):
            currentCrane = self.cranes[i - 1]
            num = len(currentCrane.list_of_containers)
            if num > maxNumOfContainers:
                maxNumOfContainers = num

        numOfIterations = int(maxNumOfContainers / self.bc)
        for j in range(0, numOfIterations + 1):
            for craneIndex in range(1, self.nq + 1):
                sublist = self.cranes[craneIndex - 1].list_of_containers[j * self.bc: (j + 1) * self.bc]
                for c in sublist:
                    self.containers.append(c)

        self.R = int(f.readline())
        for k in range(0, self.R):
            [x1, y1, x2, y2] = map(int, f.readline().split())
            numC += 1
            c = Container(numC -1, "C" + str(numC), "R", None, Location(x1, y1), Location(x2, y2), True, container_above=True)
            for container in self.containers:
                if str(container.start_position) == str(c.start_position):
                    if container.container_above == None:
                        container.container_above = c
                        c.container_under = container
                    else:
                        container.container_above.container_above = c
                        c.container_under = container.container_above
                    break
            # self.containers.insert(0, c)
            self.containers.append(c)

        # automatic travel time computation
        if compute_times:
            self.calculate_all_travel_times()    # automatic travel time computation

    def calculate_all_travel_times(self):
        self.LoadingCranes = []
        self.UnloadingCranes = []
        for c in self.cranes:
            if c.name.startswith("L"):
                self.LoadingCranes.append(c)
            else:
                self.UnloadingCranes.append(c)

        self.temlist = []
        for c in self.containers:
            if c.is_job == True:
                self.temlist.append(c)

        self.Jc = {}
        for crane in self.cranes:
            if crane.kind == "U":
                self.Jc.update(
                    {crane: [container for container in crane.list_of_containers if not container.is_in_buffer]})
            else:
                self.Jc.update({crane: [container for container in crane.list_of_containers]})

        self.Jbc = {}
        for crane in self.cranes:
            self.Jbc.update({crane: [container for container in crane.list_of_containers if container.is_in_buffer]})

        self.Jvc = {}
        for crane in self.LoadingCranes:
            self.Jvc.update({crane: []})

        self.Jqc = {}
        for crane in self.UnloadingCranes:
            self.Jqc.update({crane: []})

        self.Jlc = {}
        for crane in self.LoadingCranes:
            self.Jlc.update({crane: crane.Jbc})

        self.JUc = {}
        for crane in self.LoadingCranes:
            self.JUc.update({crane: []})
        for crane in self.UnloadingCranes:
            self.JUc.update({crane: crane.Jbc + self.Jqc[crane]})

        self.Jl = [a for i in self.LoadingCranes for a in i.list_of_containers if a not in self.Jlc[i]]

        self.Ju = [a for i in self.UnloadingCranes for a in i.list_of_containers if a.is_in_buffer is False] + [a for i in self.UnloadingCranes for a in self.JUc[i]]

        self.J = self.Jl + self.Ju

        self.R = []
        for container in self.containers:
            if container.kind == "R":
                self.R.append(container)

        self.RJ = {}
        for i in self.J:
            self.RJ[i] = []
        for r in self.R:
            for i in self.J:
                if str(i.start_position) == str(r.start_position):
                    self.RJ[i].append(r)

        self.A = [(i, j) for i in self.J + self.R + self.scs for j in self.J + self.R if i != j]

        self.Jcall = [i for a in self.cranes for i in self.Jc[a]]
        self.JUall = [a for i in self.cranes for a in self.JUc[i]]

        # All containers that interact with the buffer
        self.AllContbufint = self.Jcall + self.JUall
        self.AllContbufintUNL = [i for a in self.LoadingCranes for i in self.Jc[a]] + [i for a in self.UnloadingCranes for i in self.JUc[a]]
        self.AllContbufintLOA = [i for a in self.LoadingCranes for i in self.Jc[a]]

        # For each crane
        self.AllContBufintCranes = {}
        for a in self.cranes:
            self.AllContBufintCranes[a] = [i for i in self.Jc[a]] + [i for i in self.JUc[a]]

        self.forbinbyCranes = {}
        for a in self.cranes:
            self.forbinbyCranes[a] = [(i, j) for i in self.AllContBufintCranes[a] for j in self.AllContBufintCranes[a]
                                      if i != j]

        self.foroutbyCranes = {}
        for a in self.cranes:
            self.foroutbyCranes[a] = [(i, j) for i in self.AllContBufintCranes[a] for j in self.AllContBufintCranes[a]
                                      if i != j]

        self.forbin = [i for a in self.cranes for i in self.forbinbyCranes[a]]

        self.forout = [i for a in self.cranes for i in self.foroutbyCranes[a]]

        self.JR = [i for i in self.J if i not in self.JUall]

        # tij Unloaded times of SCs (a movement without carrying any container)
        self.Tunloaded = {}

        for i in self.J + self.R:
            self.Tunloaded[i] = {}
            for j in self.J + self.R:
                if i != j:
                    self.Tunloaded[i].update({j: i.end_position.distance(j.start_position)})
        for i in self.scs:
            self.Tunloaded[i] = {}
            for j in self.J + self.R:
                self.Tunloaded[i].update({j: i.start_position.distance(j.start_position)})

        self.tjob = {i: i.start_position.distance(i.end_position) * self.pv + 2 * self.tv for i in self.J + self.R}


if __name__ == "__main__":
    probleminstance = MSCRBProblem()
    probleminstance.read_from_file(
        "instances/4SEED_3QC_9SC_4BC_0.1R_8J.txt"
    )
    breakpoint()  # ← programmatic breakpoint