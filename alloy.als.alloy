
//SIGNATURES

//Define type sex
abstract sig Sex {}
one sig Male extends Sex{}
one sig Female extends Sex{}

//String type abstraction
sig StringLetter{}

sig Location{
	latitude: one Int,
	longitude: one Int
} 
{	
	latitude >= -90
	latitude <= 90
	longitude >= -180
	longitude <= 180
}

abstract sig Mean{
	capacity: one Int,
	available_seats: one Int
}
{
	capacity>0
	available_seats>=0
	available_seats<=capacity
}

sig TRAIN extends Mean {}
sig UNDERGROUND extends Mean {}
sig TRAM extends Mean {}
sig BUS extends Mean {}
sig TAXI extends Mean {}
sig CARSHARING extends Mean {}
sig BIKESHARING extends Mean {}
sig PLANE extends Mean {}
sig FERRY extends Mean {}
sig BYWALK extends Mean {}

sig Meeting{
	name: one StringLetter,
	insertionTime: one Int,
	start: one Int,
	end: one Int,
	place: one Location,
	people: Int,
	transportMode: some Mean,
}
{
	insertionTime>=0
	start>=0
	end>0
	end>start
}

//Supposing that duration is an integer attribute
sig Break{
	name: one StringLetter,
	insertionTime: one Int, //date of insertion the break into the calendar
	startAtLeast: one Int,
	endAtMost: one Int,
	start:one Int,
	end: one Int,
	duration: one Int
}
{
	insertionTime >= 0
	start < end
	startAtLeast < endAtMost
	start >= 0
	end > 0
	startAtLeast >= 0
	endAtMost > 0
	duration > 0
	duration = end - start
	start >= startAtLeast 
	end <= endAtMost
}

sig ServerCalendar{
	meetingEvents: set Meeting,
	breakEvents: set Break,
	now: one Int //current date
}
{
	#meetingEvents > 0
	#breakEvents > 0
	now >= 0
}

sig User{
	firstName: one StringLetter,
	lastName: one StringLetter,
	dateOfBirth: one Int,
	sex: one Sex,
	mailAddress: one StringLetter,
	password: one StringLetter,
	drivingLicenceNumber: lone Int,
	userMeeting: some Meeting,
	userBreak: one Break,
	userMeans: some Mean
}
{
	drivingLicenceNumber > 0
}

// PREDICATES

pred insertMeeting [s, s': ServerCalendar, m: Meeting] {
    s'.meetingEvents = s.meetingEvents + m
    m.insertionTime >= s.now
    m.insertionTime <= s'.now
}

pred insertBreak [s, s': ServerCalendar,b: Break] {
    s'.breakEvents = s.breakEvents + b
    b.insertionTime >= s.now
    b.insertionTime <= s'.now
}

pred removeMeeting [s, s': ServerCalendar, m: Meeting] {
    s'.meetingEvents = s.meetingEvents - m
}

pred removeBreak [s, s': ServerCalendar, b: Break] {
    s'.breakEvents = s.breakEvents - b
}

pred overlapsMM[m1, m2: Meeting] {
    (m1.start < m2.start and m1.end  >m2.start) or
	(m1.start >= m2.start and m1.start < m2.end)
}

pred overlapsMB[m: Meeting, b: Break] {
    (m.start < b.start and m.end > b.start) or
	(m.start >= b.start and m.start < b.end)
}

pred overlapsBB[b1, b2: Break] {
    (b1.start < b2.start and b1.end  >b2.start) or
	(b1.start >= b2.start and b1.start < b2.end)
}

//FACTS

//No two distinct overlapping position
fact NoPositionOverlapping{
	no disj pos1, pos2: Location|
	(pos1.latitude = pos2.latitude and pos1.longitude = pos2.longitude)
}

//No two distinct coinciding users
fact UniqueUser{
	no disj us1, us2: User|
	(us1 != us2 and 
	(us1.mailAddress = us2.mailAddress or
	us1.drivingLicenceNumber = us2.drivingLicenceNumber))
}

//No two distinct overlapping meeting
fact UniqueMeeting{
	no disj meet1, meet2: Meeting|
	(meet1!=meet2 and
	(meet1.start = meet2.start or
	meet1.end = meet2.end))
}

//No two distinct overlapping break
fact UniqueBreak{
	no disj br1, br2: Break|
	(br1 != br2 and
	(br1.startAtLeast = br2.startAtLeast or
	br1.endAtMost = br2. endAtMost ))
}

//No meeting overlapping meeting
fact NoMeetingOverlappingMeeting {
	no disj m1, m2:Meeting | overlapsMM[m1, m2]
}

//No meeting overlapping break
fact NoMeetingOverlappingBreak {
	no disj m:Meeting, b: Break | overlapsMB[m, b]
}

//No break overlapping break
fact NoBreakOverlappingBreak {
	no disj b1, b2: Break | overlapsBB[b1, b2]
}

//time for break
fact TimeBreak{
	all b:Break | ((b.endAtMost - b.startAtLeast) >= b.duration)
}

//date of meeting is after date of insertion
fact meetingMustBeInFuture{
	all m: Meeting | (m.insertionTime <= m.start)
}

//date of meeting is after date of insertion
fact breakMustBeInFuture{
	all b: Break | (b.insertionTime <= b.start)
}

//Server Calendar contains all meetings
fact containAllMeeting {
	all m: Meeting, c: ServerCalendar | (m in c.meetingEvents)
}

//Server Calendar contains all breaks
fact containAllBreak {
	all b: Break, c: ServerCalendar | (b in c.breakEvents)
}

//duration break
fact breakDuration{
	all b: Break | (b.end - b.start = b.duration)
}

//The number of people must be lower than the capacity of mean
fact ContainPeople{
	all m: Meeting, t: Mean | (m.people <= t.capacity)
}

//The number of people must be lower than the available seats
fact AvailablePeople{
	all m:Meeting, t: Mean| (m.people <= t.available_seats)
}


//ASSERTIONS

//No overlps
assert noOverlapping {
  no disj m1, m2: Meeting | overlapsMM[m1, m2]
  no disj m: Meeting, b: Break | overlapsMB[m, b]
  no disj b1, b2: Break | overlapsBB[b1, b2]
}

//Available seats imply higher capacity of the means of transport
assert Available {
	all m:Meeting, t: Mean | ((m.people <= t.available_seats) implies (m.people <= t.capacity))
}

//Duration of break is equal to difference between end and start time
assert DurationBreak{
	all b: Break | (b.duration = (b.end - b.start))
}


pred show() {}

//run show for 5 
check noOverlapping for 5
