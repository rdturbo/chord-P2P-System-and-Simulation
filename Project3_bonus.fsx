#time "on"
#r "nuget: Akka.FSharp" 
#r "nuget: Akka.TestKit"

open System
open System.Collections.Generic
open System.Collections.Concurrent
open System.Security.Cryptography
open System.Numerics
open Akka.Actor
open Akka.Configuration
open Akka.FSharp
open Akka.TestKit

let timer = Diagnostics.Stopwatch.StartNew()
let system = ActorSystem.Create("FSharp")
let randPeerToPeer = Random()
let mutable countResponce = 0 
let mutable globalWorkerDict = new Dictionary<bigint, IActorRef>()
let mutable globalWorkerDoneList = new List<int>()


type DispatcherInputMsg = int * int * int
type DispatcherMessageChord = bigint * int * List<bigint> * bigint * bigint * int * List<bigint>
type DispatcherMessageChordLate = bigint * int * int
type RequestMessageChord = string * bigint * bigint * int * bigint
type SuccessorFoundMessageChord = bigint * bigint * List<bigint>
type FixFingerTableMessage = bigint * bigint * bigint
type FinishedMessage = int * bigint
type RequestReachedDestinationMessage = int * string * bigint
type CheckMessageRecivedMessage = string * bigint
type FindSuccessorMessageChord = bigint * bigint
type MessagesOfActor = 
    | Finished of FinishedMessage
    | StartMessage of string
    | JoinMessage of List<bigint>
    | RequestReachedDestination of RequestReachedDestinationMessage
    | WakeTheNode of int
    | DispatcherInput of DispatcherInputMsg
    | MessageToWorker of DispatcherMessageChord
    | MessageToWorkerLate of DispatcherMessageChordLate
    | RequestMessage of RequestMessageChord
    | FindSuccessorMessage of FindSuccessorMessageChord
    | SuccessorFoundMessage of SuccessorFoundMessageChord
    | Stabilize of int
    | StabilizeSuccessorSendPredecessor of bigint
    | StabilizeAskSuccessor of bigint
    | StabilizeNotify of bigint
    | FixFingerTableRequest of FixFingerTableMessage
    | FixFingerTable of int
    | FixFingerTableRequestFoundDestination of bigint
    | CheckPredecessor of string
    | SuccessorCheckingPredecessor of string
    | PredecessorReply of string
    | CheckMessageRecived of CheckMessageRecivedMessage
    | RequestRecived of bigint
    | CheckFailedRequests of int
    | DieNode of int

let byteConvertToString x = 
    BitConverter.ToString(x).Replace("-", "").ToLower()

let stringConvertToByte (str: string) = 
    System.Text.Encoding.ASCII.GetBytes(str)

let randomStr = 
            let chars = "abcdefghijklmnopqrstuvwxyz0123456789"
            let charsLen = chars.Length
            fun len -> 
                let randomChars = [|for i in 0..len -> chars.[randPeerToPeer.Next(charsLen)]|]
                String(randomChars)

let decideDesitnation (lowerDimHashedVal: bigint) (current: bigint) (predecessor: bigint) (successor: bigint) (fingerTable: List<bigint>) (successorList: List<bigint>) =
    let mutable destination = current
    let mutable allFingers = HashSet<bigint>()
    let mutable allFingersList = List<bigint>()
    for item in fingerTable do
        allFingers.Add(item) |> ignore
    for item in successorList do
        allFingers.Add(item) |> ignore
    for item in allFingers do 
        allFingersList.Add(item)
    allFingersList.Sort()
    if  not(predecessor = bigint(-1)) && ((predecessor < current && (lowerDimHashedVal > predecessor && lowerDimHashedVal <= current)) || (predecessor > current && ((lowerDimHashedVal <= current) ||( lowerDimHashedVal > current && lowerDimHashedVal > predecessor)))) then
        destination <- current
    else if (current < successor && (lowerDimHashedVal > current && lowerDimHashedVal <= successor)) || (current > successor  && ((lowerDimHashedVal < current && lowerDimHashedVal <= successor) || lowerDimHashedVal > current )) then
        destination <- successor
    else if (allFingersList.Count > 0 && lowerDimHashedVal < allFingersList.Item(0)) || (allFingersList.Count - 1 > 0 && lowerDimHashedVal > allFingersList.Item(allFingersList.Count - 1)) then
        destination <- allFingersList.Item(allFingersList.Count - 1)
    else
        for i in 0 .. allFingersList.Count - 2 do
            if i >= 0 && lowerDimHashedVal > allFingersList.Item(i) && lowerDimHashedVal <= allFingersList.Item(i + 1) then
                destination <- allFingersList.Item(i)
    destination
    
let workerChord(mailbox: Actor<_>) = 
                let mutable messageRecivedCount = 0
                let mutable dispatcher = mailbox.Self
                let mutable fingerTable = new List<bigint>()
                let mutable successorList = new List<bigint>()
                let mutable requestDict = new Dictionary<string, int>()
                let mutable requestDestinationDict = new Dictionary<int, bigint>()
                let mutable currentRequestIndex = 0
                let mutable nodeAddress = bigint(-1)
                let mutable m = -1
                let mutable numRequests = -1
                let mutable predecessor = bigint(-1)
                let mutable successor = bigint(-1)
                let mutable totalHops = 0
                let mutable sentRequestCount = 0
                let mutable predecessorExists = 1
                let mutable nodeState = 1
                let mutable randomNodes = List<bigint>()
                let rec loop() = actor {
                        mailbox.Context.SetReceiveTimeout(TimeSpan.FromSeconds 1000.0)
                        let! message = mailbox.Receive()
                        if dispatcher = mailbox.Self then 
                            dispatcher <- mailbox.Sender()
                        if nodeState = 1 then
                            match message with
                            | MessageToWorker(nodeID, theM, fingers, pred, succ, numReq, succList) -> 
                                nodeAddress <- nodeID
                                fingerTable <- fingers
                                m <- theM
                                predecessor <- pred
                                numRequests <- numReq
                                successor <- succ
                                successorList <- succList
                            | DieNode(num) ->
                                nodeState <- 0                
                            | MessageToWorkerLate(nodeID, theM, numReq) ->
                                nodeAddress <- nodeID
                                m <- theM
                                numRequests <- numReq
                            | StartMessage(msg) ->
                                let two_to_power_m_big_int = bigint(System.Math.Pow(2.0, m |> double) |> int64)
                                if sentRequestCount < numRequests then
                                    let mutable strcon = randomStr(5)
                                    while requestDict.ContainsKey(strcon) do
                                        strcon <- randomStr(5)
                                    requestDict.Add(strcon, 0)
                                    let hashval = strcon  
                                                    |> stringConvertToByte
                                                    |> HashAlgorithm.Create("SHA1").ComputeHash
                                    let SHA1Hash = abs(bigint(hashval))
                                    let hashInLowerDim = SHA1Hash % two_to_power_m_big_int
                                    // printfn "requst %s sent to node %A" strcon hashInLowerDim                                                    
                                    let destination = decideDesitnation hashInLowerDim nodeAddress predecessor successor fingerTable successorList
                                    requestDestinationDict.Add(currentRequestIndex, destination)
                                    currentRequestIndex <- currentRequestIndex + 1
                                    globalWorkerDict.Item(destination) <! RequestMessage(strcon, hashInLowerDim, nodeAddress, 0, nodeAddress)
                                    // dispatcher <! Finished(0)
                                    system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(2000.0), mailbox.Self, CheckMessageRecived(strcon, hashInLowerDim))
                                    sentRequestCount <- sentRequestCount + 1
                                    system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(100.0), mailbox.Self, StartMessage("Another!"))
                                if sentRequestCount = 1 then
                                    system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(10.0), mailbox.Self, Stabilize(1))
                                    system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(1000.0), mailbox.Self, FixFingerTable(1))
                                    system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(500.0), mailbox.Self, CheckPredecessor("Find it!"))
                                    system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(2000.0), mailbox.Self, CheckFailedRequests(1))
                                    
                            | RequestMessage(request, hashedToLowerDim, sender, hops, prevNode) ->
                                globalWorkerDict.Item(prevNode) <! RequestRecived(nodeAddress)
                                let destination = decideDesitnation hashedToLowerDim nodeAddress predecessor successor fingerTable successorList
                                // printfn "\n\nNode %A recived request %s with hash lower dim %A from orignal sender %A with %d many hops next destination %A" nodeAddress request hashedToLowerDim sender hops destination
                                let newHops = hops + 1
                                if destination = nodeAddress then
                                    globalWorkerDict.Item(sender) <! RequestReachedDestination(newHops, request, hashedToLowerDim)
                                else
                                    requestDestinationDict.Add(currentRequestIndex, destination)
                                    currentRequestIndex <- currentRequestIndex + 1
                                    globalWorkerDict.Item(destination) <! RequestMessage(request, hashedToLowerDim, sender, newHops, nodeAddress)
                            |RequestRecived(node) ->
                                for i in 0 .. currentRequestIndex do
                                    let found, value = requestDestinationDict.TryGetValue(i)
                                    if found then
                                        if value = node then
                                            requestDestinationDict.Remove(i) |> ignore
                            |CheckFailedRequests(num)->
                                for i in 0 .. currentRequestIndex do
                                    let found, value = requestDestinationDict.TryGetValue(i)
                                    if found then
                                        if currentRequestIndex - i >= 1 then
                                            // printfn "Message failed to reach desitination %A" value
                                            if fingerTable.Contains(value) && fingerTable.Count > 1 then
                                                fingerTable.Remove(value) |> ignore
                                            if successorList.Contains(value) && successorList.Count > 1 then
                                                successorList.Remove(value) |> ignore 
                                            if successor = value then
                                                if successorList.Count > 0 then
                                                    successor <- successorList.Item(0)
                                                else
                                                    successor <- bigint(-1)
                                            if requestDestinationDict.ContainsKey(i) then
                                                requestDestinationDict.Remove(i) |> ignore
                            | RequestReachedDestination(hops, request, requestHashedLowerDimed)->
                                messageRecivedCount <- messageRecivedCount + 1
                                requestDict.Item(request) <- 1
                                totalHops <- totalHops + hops
                                if messageRecivedCount = numRequests then
                                    // printfn "%d %d" (requestDestinationDict.Count) currentRequestIndex
                                    dispatcher <! Finished(totalHops, nodeAddress)
                            | CheckMessageRecived(request, requestHashedLowerDimed) ->
                                if requestDict.Item(request) = 0 then
                                    // printfn "Message %s at node %A was not recived" request nodeAddress
                                    let destination = decideDesitnation requestHashedLowerDimed nodeAddress predecessor successor fingerTable successorList
                                    requestDestinationDict.Add(currentRequestIndex, destination)
                                    currentRequestIndex <- currentRequestIndex + 1
                                    globalWorkerDict.Item(destination) <! RequestMessage(request, requestHashedLowerDimed, nodeAddress, 0, nodeAddress)
                                    system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(2000.0), mailbox.Self, CheckMessageRecived(request, requestHashedLowerDimed))
                            | JoinMessage(randNodes) ->
                                randomNodes <- randNodes
                                if successor = bigint(-1) then
                                    let randNode = randomNodes.Item(randPeerToPeer.Next(randomNodes.Count))
                                    requestDestinationDict.Add(currentRequestIndex, randNode)
                                    currentRequestIndex <- currentRequestIndex + 1
                                    globalWorkerDict.Item(randNode) <! FindSuccessorMessage(nodeAddress, nodeAddress)
                                    system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(4000.0), mailbox.Self, JoinMessage(randomNodes))
                            | FindSuccessorMessage(node, prevSender) -> 
                                globalWorkerDict.Item(prevSender) <! RequestRecived(nodeAddress)
                                let destination = decideDesitnation node nodeAddress predecessor successor fingerTable successorList
                                if destination = nodeAddress && not (predecessor = bigint(-1)) then
                                    globalWorkerDict.Item(node) <! SuccessorFoundMessage(nodeAddress, predecessor, successorList)
                                    predecessor <- node
                                else
                                    requestDestinationDict.Add(currentRequestIndex, destination)
                                    currentRequestIndex <- currentRequestIndex + 1
                                    globalWorkerDict.Item(destination) <! FindSuccessorMessage(node, nodeAddress)
                            | SuccessorFoundMessage(succ, pred, succList) ->
                                successor <- succ
                                predecessor <- pred
                                // printfn "\n\n%A %A\n\n" successor predecessor
                                fingerTable.Add(successor)
                                successorList.Add(successor)
                                for item in succList do
                                    successorList.Add(item)
                                successorList.Sort()
                                globalWorkerDict.Item(nodeAddress) <! StartMessage("Start sending requests new node!")
                                system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(5.0), mailbox.Self, Stabilize(1))
                                system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(5.0), mailbox.Self, FixFingerTable(1))
                            | Stabilize(num)->
                                if not(successor = bigint(-1)) then
                                    globalWorkerDict.Item(successor) <! StabilizeAskSuccessor(nodeAddress)
                                    requestDestinationDict.Add(currentRequestIndex, successor)
                                    currentRequestIndex <- currentRequestIndex + 1
                                    system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(10.0), mailbox.Self, Stabilize(1))
                            | StabilizeAskSuccessor(node) ->
                                if not (predecessor = bigint(-1)) then
                                    globalWorkerDict.Item(node) <! RequestRecived(nodeAddress)
                                    globalWorkerDict.Item(node) <! StabilizeSuccessorSendPredecessor(predecessor)
                            | StabilizeSuccessorSendPredecessor(pred) ->
                                if not(nodeAddress = pred) then
                                    successor <- pred
                                    successorList.Add(pred)
                                    successorList.Sort()
                                    successorList.RemoveAt(successorList.Count - 1) 
                                requestDestinationDict.Add(currentRequestIndex, successor)
                                currentRequestIndex <- currentRequestIndex + 1
                                globalWorkerDict.Item(successor) <! StabilizeNotify(nodeAddress)
                            | StabilizeNotify(node) ->
                                globalWorkerDict.Item(node) <! RequestRecived(nodeAddress)
                                predecessor <- node
                            | FixFingerTable(msg) ->
                                let two_to_power_m_big_int = bigint(System.Math.Pow(2.0, m |> double) |> int64)
                                for f in 0 .. m - 1 do
                                    let neigborNode = (nodeAddress + bigint(System.Math.Pow(2.0, f |> double) |> int64)) % two_to_power_m_big_int
                                    globalWorkerDict.Item(successor) <! FixFingerTableRequest(nodeAddress, neigborNode, nodeAddress)
                                    requestDestinationDict.Add(currentRequestIndex, successor)
                                    currentRequestIndex <- currentRequestIndex + 1
                                system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(1000.0), mailbox.Self, FixFingerTable(1))    
                            | FixFingerTableRequest(sender, queryNode, prevSender) ->
                                globalWorkerDict.Item(prevSender) <! RequestRecived(nodeAddress)
                                let destination = decideDesitnation queryNode nodeAddress predecessor successor fingerTable successorList
                                if destination = nodeAddress then
                                    globalWorkerDict.Item(sender) <! FixFingerTableRequestFoundDestination(nodeAddress)
                                else
                                    globalWorkerDict.Item(destination) <! FixFingerTableRequest(sender, queryNode, nodeAddress)
                                    requestDestinationDict.Add(currentRequestIndex, successor)
                                    currentRequestIndex <- currentRequestIndex + 1
                            | FixFingerTableRequestFoundDestination(newFinger) ->
                                let mutable fingerFound = 0
                                for finger in fingerTable do
                                    if finger = newFinger then
                                        fingerFound <- 1
                                if not (fingerFound = 1) then 
                                    fingerTable.Add(newFinger)
                                    fingerTable.Sort()
                                    if successorList.Count < 2 then
                                        successorList.Add(newFinger)
                                        successorList.Sort()
                            | CheckPredecessor(msg) ->
                                if not (predecessor = bigint(-1)) then
                                    if predecessorExists = 1 then
                                        globalWorkerDict.Item(predecessor) <! SuccessorCheckingPredecessor("Still there?")
                                        predecessorExists <- 0
                                    else
                                        // printfn "Lost predecessor..."
                                        predecessor <- bigint(-1)
                                system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(500.0), mailbox.Self, CheckPredecessor("Find it!"))
                            | PredecessorReply(msg) ->
                                predecessorExists <- 1
                            | SuccessorCheckingPredecessor(msg) ->
                                globalWorkerDict.Item(successor) <! PredecessorReply("I am here!")
                            | _ ->  printfn "An error occured at worker %A" nodeAddress    
                        return! loop()
                    }
                loop()

let DispatcherChord(mailbox: Actor<_>) = 
            let mutable numNodes = 0
            let mutable numRequest = 0
            let mutable wakeUpCount = 0
            let mutable workerIDDict = new Dictionary<int, bigint>()
            let mutable totalHops = 0L
            let mutable remainingNodes = 0
            let mutable deadCount = 0
            let rec loop() = actor {
                    mailbox.Context.SetReceiveTimeout(TimeSpan.FromSeconds 10000.0)
                    let! message = mailbox.Receive()
                    match message with
                    | DispatcherInput(n, numReq, deadNum) ->
                        deadCount <- deadNum
                        if n <= 100 then
                            numNodes <- (n - ((0.1 * (n |> float)) |> int))
                            remainingNodes <- (0.1 * (n |> float)) |> int
                            printfn "n - %d | starting nodes - %d | joining nodes - %d | dead nodes - %d" n numNodes remainingNodes deadNum
                        else 
                            numNodes <- n - 10
                            remainingNodes <- 10
                            printfn "n - %d | starting nodes - %d | joining nodes - %d | dead nodes - %d" n numNodes remainingNodes deadNum

                        numRequest <- numReq
                        let m = (ceil(System.Math.Log(numNodes |> float, 2.0 )) * 3.0) |> int
                        let two_to_power_m_int = System.Math.Pow(2.0, m |> double) |> int64
                        let two_to_power_m_big_int = bigint(System.Math.Pow(2.0, m |> double) |> int64)
                        printfn "m is %d" m
                        for i in 1 .. numNodes do
                            let perName = "rupayandas"
                            let strcon = perName + ";" + (i).ToString()                  
                            let hashval = strcon  
                                            |> stringConvertToByte
                                            |> HashAlgorithm.Create("SHA1").ComputeHash
                            let SHA1ID = abs(bigint(hashval))
                            let actualWorkerID = SHA1ID % two_to_power_m_big_int
                            globalWorkerDict.Add(actualWorkerID, spawn system (sprintf "Worker_%A" actualWorkerID) workerChord)
                            workerIDDict.Add(i, actualWorkerID)
                        let mutable workerIDsList = new List<bigint>()
                        for item in workerIDDict.Values do
                            workerIDsList.Add(item)
                        workerIDsList.Sort()
                        for iiii in 1 .. deadCount do
                            let deadIndex = randPeerToPeer.Next(numNodes - 1)
                            globalWorkerDict.Item(workerIDDict.Item(deadIndex)) <! DieNode(1)
                        for j in 0 .. numNodes - 1 do
                            let mutable fingerTableSet = new HashSet<bigint>()
                            let mutable fingerTable = new List<bigint>()
                            let mutable successorList = new List<bigint>()
                            for f in 0 .. m - 1 do
                                let neigbor_node = (workerIDDict.Item(j + 1) + bigint(System.Math.Pow(2.0, f |> double) |> int64)) % two_to_power_m_big_int
                                let mutable first_bigger_found = 0
                                for t in 0 .. workerIDsList.Count - 1 do
                                    if neigbor_node <= workerIDsList.Item(t) && first_bigger_found = 0 then
                                        fingerTableSet.Add(workerIDsList.Item(t)) |> ignore
                                        first_bigger_found <- 1
                                if neigbor_node > workerIDsList.Item(workerIDsList.Count - 1) then 
                                    fingerTableSet.Add(workerIDsList.Item(0)) |> ignore
                            for item in fingerTableSet do
                                fingerTable.Add(item)
                            fingerTable.Sort()
                            let nodeIndexInSortedList = workerIDsList.IndexOf(workerIDDict.Item(j + 1))
                            for iii in 1 .. (ceil(System.Math.Log(numNodes |> float, 2.0 )))|> int do
                                let indexofSuccessor = (nodeIndexInSortedList + iii) % workerIDsList.Count
                                successorList.Add(workerIDsList.Item(indexofSuccessor))

                            let mutable predecessor = bigint(-1)
                            
                            if workerIDsList.IndexOf(workerIDDict.Item(j + 1)) > 0 then
                                predecessor <- workerIDsList.Item(workerIDsList.IndexOf(workerIDDict.Item(j + 1)) - 1)
                            else
                                predecessor <- workerIDsList.Item(workerIDsList.Count - 1)
                            let mutable successor = bigint(-1)
                            if workerIDsList.IndexOf(workerIDDict.Item(j + 1)) + 1 < workerIDsList.Count then
                                successor <- workerIDsList.Item(workerIDsList.IndexOf(workerIDDict.Item(j + 1)) + 1)
                            else
                                successor <- workerIDsList.Item(0)
                            globalWorkerDict.Item(workerIDDict.Item(j + 1)) <! MessageToWorker((workerIDDict.Item(j + 1), m, fingerTable, predecessor, successor, numRequest, successorList))
                        
                        for ii in 1 .. numNodes do 
                            globalWorkerDict.Item(workerIDDict.Item(ii)) <! StartMessage("Start!")
                        for i in numNodes + 1 .. numNodes + remainingNodes do
                            let perName = "rupayandas"
                            let strcon = perName + ";" + (i).ToString()                  
                            let hashval = strcon  
                                            |> stringConvertToByte
                                            |> HashAlgorithm.Create("SHA1").ComputeHash
                            let SHA1ID = abs(bigint(hashval))
                            let actualWorkerID = SHA1ID % two_to_power_m_big_int
                            globalWorkerDict.Add(actualWorkerID, spawn system (sprintf "Worker_%A" actualWorkerID) workerChord)
                            workerIDDict.Add(i, actualWorkerID)
                            globalWorkerDict.Item(workerIDDict.Item(i)) <! MessageToWorkerLate((workerIDDict.Item(i), m, numRequest))
                        let mutable workerIDsListUpdated = new List<bigint>()
                        for item in workerIDDict.Values do
                            workerIDsListUpdated.Add(item)
                        workerIDsListUpdated.Sort()
                        for ii in numNodes + 1 .. numNodes + remainingNodes do
                            let mutable randNodes =new List<bigint>() 
                            for iiii in 0 .. m do 
                                randNodes.Add(workerIDsList.Item(randPeerToPeer.Next(workerIDsList.Count - 1)))
                            globalWorkerDict.Item(workerIDDict.Item(ii)) <! JoinMessage(randNodes)
                            // printfn "%A asking %A to find successor"  (workerIDDict.Item(ii)) randNode
                    | Finished(nodeTotalHops, finishedNode) ->
                        countResponce <- countResponce + 1
                        if countResponce <= numNodes + remainingNodes - deadCount then
                            printfn "%A %d finished  with %d many hops" finishedNode countResponce nodeTotalHops
                            totalHops <- totalHops + (nodeTotalHops |> int64)
                            if countResponce = numNodes + remainingNodes - deadCount then
                                let averageHops = (totalHops |> float) / (((numNodes + remainingNodes - deadCount) |> float) * (numRequest |> float))
                                printfn "\n\n\n\nTotal hops: %d Average hops were:  %f\n\n\n\n" totalHops averageHops
                                mailbox.Context.System.Terminate() |> ignore
                    | _ -> printfn "An error occured at dipatcher"
                    return! loop()
                }
            loop()

let numNodes = fsi.CommandLineArgs.[1] |>int
let numReq = fsi.CommandLineArgs.[2] |>int
let deadCount = fsi.CommandLineArgs.[3] |>int
let Boss  = spawn system "Boss" DispatcherChord
Boss <! DispatcherInput(numNodes, numReq, deadCount)
system.WhenTerminated.Wait()
