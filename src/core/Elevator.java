package core;

import event.Callback;
import event.EventEmitter;

import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

public class Elevator extends EventEmitter{
    // Request list for elevator
    private /*@ spec_public @*/ List<Request> requests = new LinkedList<Request>();
    /*@ spec_public @*/ ElevatorStatus status = new ElevatorStatus();

    /**
     * Start elevator
     */
    /*@	requires (status != null && status.currentFloor >= 0);
      @	assignable requests;
      @	assignable status.targetFloor;
      @ ensures status.targetFloor == requests.get(0).getStopFloor(); @*/
    public void launch() {
        new Thread(new ElevatorThread(this)).start();
        this.emit(ElevatorEvent.LAUNCH, status.getCurrentFloor());

        this.on(ElevatorEvent.OPEN, data -> {
            int currentFloor = (Integer) data;
            requests = requests.stream().filter((req) -> !(req.stopFloor == currentFloor))
                    .collect(Collectors.toList());
        });

        this.on(ElevatorEvent.CLOSE, data -> updateTarget());
    }

    /**
     * Called when the floor button is pressed
     * @param direction
     * @param currentFloor
     * @param presser
     * @return
     */
    /*@	requires (direction == UP || direction == DOWN);
      @	requires currentFloor >= 0;
      @	requires presser != null;
      @ assignable requests;
      @ assignable status.targetFloor;
      @ ensures requests.size() > \old(requests).size();
      @ ensures status.targetFloor == requests.get(0).getStopFloor();
      @ ensures \result == Elevator; @*/
    public Elevator outerPress(Direction direction, int currentFloor, Human presser) {
        OuterRequest req = new OuterRequest()
                .setDirection(direction)
                .setCurrentFloor(currentFloor)
                .setPresser(presser);
        requests.add(req);

        this.emit(ElevatorEvent.OUTER_PRESSED, req);
        updateTarget();

        return this;
    }

    /**
     * Called when the elevator button is pressed
     * @param targetFloor
     * @param presser
     * @return
     */
    /*@	requires requests != null;
      @	requires targetFloor >= 0;
      @	requires presser != null;
      @ assignable requests;
      @ assignable status.targetFloor;
      @ ensures requests.size() > \old(requests).size();
      @ ensures status.targetFloor == requests.get(0).getStopFloor();
      @ ensures \result == Elevator; @*/
    public Elevator innerPress(int targetFloor, Human presser) {
        InnerRequest req = new InnerRequest()
                .setCurrentFloor(status.getCurrentFloor())
                .setTargetFloor(targetFloor)
                .setPresser(presser);
        requests.add(req);

        this.emit(ElevatorEvent.INNER_PRESSED, req);
        updateTarget();

        return this;
    }

    /**
     * update the target when the elevator is moving
     */
    /*@	requires (requests != null
      @		|| requests.size() > 0);
      @	assignable requests;
      @	assignable status.targetFloor;
      @ ensures status.targetFloor == requests.get(0).getStopFloor(); @*/
    private void updateTarget(){
        Request first;
        // sort the requests
        sort(requests);
        if(requests.size() == 0) return;

        first = requests.get(0);
        // set the targetFloor
        status.setTargetFloor(first.getStopFloor());
    }

    /**
     * sorts the requests
     * @param requests
     */
    /*@	requires (requests != null
      @		|| requests.size() > 0);
      @	assignable requests; @*/
    private void sort(List<Request> requests){
        int currentFloor = status.getCurrentFloor();
        Direction currentDirection = status.getDirection();

        // Going up, for example, all the requests should be:
        // 1. Floor request is bigger than the elevator current floor
        // 2. Going down request
        // 3. Going up request, but the floor request is lower than the elevator current floor

        // first case
        List<Request> list1 = requests.stream().filter( req -> {
            // same direction
            boolean isSame = req.getDirection() == currentDirection;
            // it has priority
            boolean isSuper = (currentDirection == Direction.UP)?
                    (req.getStopFloor() >= currentFloor)
                    :(req.getStopFloor() < currentFloor);

            return isSame && isSuper;
        }).sorted( (lhs,rhs) -> {
            if(currentDirection == Direction.UP){
                return lhs.getStopFloor() - rhs.getStopFloor();
            }else{
                return -(lhs.getStopFloor() - rhs.getStopFloor());
            }
        }).collect(Collectors.toList());

        // second case
        List<Request> list2 = requests.stream().filter( req -> {
            // reverse direction
            boolean isSame = (req.getDirection() == currentDirection);
            return !isSame;
        }).sorted( (lhs,rhs) -> {
            // elevator has priority
            if(currentDirection == Direction.UP){
                return -(lhs.getStopFloor() - rhs.getStopFloor());
            }else{
                return lhs.getStopFloor() - rhs.getStopFloor();
            }
        }).collect(Collectors.toList());

        // third case
        List<Request> list3 = requests.stream().filter( req -> {
            // same direction
            boolean isSame = req.getDirection() == currentDirection;
            // it has priority
            boolean isSuper = (currentDirection == Direction.UP)?
                    (req.getStopFloor() >= currentFloor)
                    :(req.getStopFloor() < currentFloor);

            return isSame && !isSuper;
        }).sorted( (lhs,rhs) -> {
            // elevator has priority
            if(currentDirection == Direction.UP){
                return lhs.getStopFloor() - rhs.getStopFloor();
            }else{
                return -(lhs.getStopFloor() - rhs.getStopFloor());
            }
        }).collect(Collectors.toList());

        requests.clear();

        // combining all the requests
        requests.addAll(list1);
        requests.addAll(list2);
        requests.addAll(list3);
    }

    /*@	requires type != null;
      @*/
    @SuppressWarnings("unchecked")
	public <T> void emit(ElevatorEvent type, T... data) {
        super.emit(type, data);
    }
    
    /*@	requires type != null;
      @*/
    @SuppressWarnings("rawtypes")
	public void on(ElevatorEvent type, Callback callback) {
        super.on(type, callback);
    }
}
