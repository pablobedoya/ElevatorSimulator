package core;

/**
 * Objeto de estado do elevador
 */
public class ElevatorStatus {
    private /*@ spec_public @*/ int currentFloor = 1;
    private /*@ spec_public @*/ Direction direction = Direction.UP;
    private /*@ spec_public @*/ int targetFloor = 0;
    private /*@ spec_public @*/ boolean isOpen = false;
    private /*@ spec_public @*/ boolean isMoving = true;
    
    /*@	ensures \result == currentFloor; @*/
	public /*@ pure @*/ int getCurrentFloor() {
		return currentFloor;
	}
	
	/*@ requires curFloor >= 0;
	  @	ensures currentFloor == curFloor; @*/
	public void setCurrentFloor(int curFloor) {
		currentFloor = curFloor;
	}
	
	/*@	ensures \result == direction; @*/
	public /*@ pure @*/ Direction getDirection() {
		return direction;
	}
	
	/*@ requires d != null;
	  @	ensures direction == d; @*/
	public void setDirection(Direction d) {
		direction = d;
	}
	
	/*@	ensures \result == targetFloor; @*/
	public /*@ pure @*/ int getTargetFloor() {
		return targetFloor;
	}
	
	/*@ requires targFloor >= 0;
	  @	ensures targetFloor == targFloor; @*/
	public void setTargetFloor(int targFloor) {
		targetFloor = targFloor;
	}
	
	/*@	ensures \result == isOpen; @*/
	public /*@ pure @*/ boolean isOpen() {
		return isOpen;
	}
	
	/*@	ensures isOpen == open; @*/
	public void setOpen(boolean open) {
		isOpen = open;
	}
	
	/*@	ensures \result == isMoving; @*/
	public /*@ pure @*/ boolean isMoving() {
		return isMoving;
	}
	
	/*@	ensures isMoving == moving; @*/
	public void setMoving(boolean moving) {
		isMoving = moving;
	}
}
