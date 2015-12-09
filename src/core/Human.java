package core;

import event.EventEmitter;

/**
 * Passageiros do elevador
 */
public class Human extends EventEmitter{
    private /*@ spec_public @*/ int currentFloor = 0;
    private /*@ spec_public @*/ int targetFloor = 0;
    private /*@ spec_public @*/ int weight = 0;
    private /*@ spec_public @*/ String name;
    
  //@ public invariant 0 <= targetFloor;
  //@ public invariant 0 <= currentFloor;
  //@ public invariant 0 < name.length();

  //@ public invariant 0 <= weight && weight <= 150;
    
    private /*@ spec_public non_null @*/ Elevator elevator;

    public Human() {
        this.on(ElevatorEvent.ENTER, data -> {
            // Pressionar o botao do elevador
            elevator.innerPress(targetFloor, this);
        });
    }

    /**
     * Deixar o passageiro no piso e pressionar o botao do elevador
     */
    public Human go() {
        elevator.outerPress(currentFloor > targetFloor ? Direction.DOWN : Direction.UP,
                currentFloor, this);
        return this;
    }

    /**
     * Definir a acao de retorno de chamada para varios elevadores de passageiros
     */
    private /*@ pure @*/ void setActions() {
        elevator.on(ElevatorEvent.OPEN, data -> {
            int openFloor = (Integer) data;

            // Se o elevador parou no seu piso
            if (openFloor == currentFloor) {
                // Entre no elevador e acione seu evento de entrada
                elevator.emit(ElevatorEvent.ENTER, this);
                this.emit(ElevatorEvent.ENTER, this);

            } else if (openFloor == targetFloor) {
                // Deixar o elevador
                elevator.emit(ElevatorEvent.LEAVE, this);
            }
        });
    }

    /*@	ensures \result == currentFloor; @*/
    public /*@ pure @*/ int getCurrentFloor() {
        return currentFloor;
    }

    /*@ requires curFloor >= 0;
	  @	ensures currentFloor == curFloor;
	  @	ensures \result == Human; @*/
    public Human setCurrentFloor(int curFloor) {
        currentFloor = curFloor;
        return this;
    }

    /*@	ensures \result == targetFloor; @*/
    public /*@ pure @*/ int getTargetFloor() {
        return targetFloor;
    }
    
    /*@ requires targFloor >= 0;
	  @	ensures targetFloor == targFloor;
	  @	ensures \result == Human; @*/
    public Human setTargetFloor(int targFloor) {
        targetFloor = targFloor;
        return this;
    }

    /*@	ensures \result == weight; @*/
    public /*@ pure @*/ int getWeight() {
        return weight;
    }

    /*@ requires w >= 0;
	  @	ensures weight == w;
	  @	ensures \result == Human; @*/
    public Human setWeight(int w) {
        weight = w;
        return this;
    }

    /*@	ensures \result == elevator; @*/
    public /*@ pure @*/ Elevator getElevator() {
        return elevator;
    }

    /*@ requires elev != null;
	  @	ensures elevator == elev;
	  @	ensures \result == Human; @*/
    public Human setElevator(Elevator elev) {
        elevator = elev;
        setActions();

        return this;
    }

    /*@	ensures \result == name; @*/
    public /*@ pure @*/ String getName() {
        return name;
    }

    /*@ requires n != "";
	  @	ensures name.equals(n);
	  @	ensures \result == Human; @*/
    public Human setName(String n) {
        name = n;
        return this;
    }
}
