package util;

import core.*;

import java.text.MessageFormat;

/**
 * System's monitor
 */
public class Watcher {
	/*@	requires elevator != null; @*/
    public /*@ pure @*/ void watch(Elevator elevator) {
        elevator.on(ElevatorEvent.LAUNCH, data -> {
            int floor = (Integer)data;
            System.out.println("/\\ "+ floor);
        });

        // floor button pressed
        elevator.on(ElevatorEvent.OUTER_PRESSED, data -> {
            OuterRequest req = (OuterRequest)data;
            Human human = req.getPresser();
            String msg = MessageFormat.format("{0} quer {1} do piso {2}",
            		human.getName(), req.getDirection() == Direction.UP ? "subir" : "descer",
            				req.getCurrentFloor());
            System.out.println(msg);
        });

        // elevator's button pressed
        elevator.on(ElevatorEvent.INNER_PRESSED, data -> {
            InnerRequest req = (InnerRequest)data;
            Human human = req.getPresser();
            String msg = MessageFormat.format("{0} estah indo para o piso {1}",
                    human.getName(), req.getTargetFloor());
            System.out.println(msg);
        });

        // elevator's moving
        elevator.on(ElevatorEvent.MOVING, data -> {
            int floor = (Integer)data;
            System.out.println("elevador indo para o piso " + floor);
        });

        // waiting
        elevator.on(ElevatorEvent.PENDING, data -> System.out.println("aguardando"));

        // open door
        elevator.on(ElevatorEvent.OPEN, data -> {
            int floor = (Integer)data;
            System.out.println("Porta aberta no piso " + floor);
        });

        // close door
        elevator.on(ElevatorEvent.CLOSE, data -> {
            int floor = (Integer)data;
            System.out.println("Porta fechada no piso " + floor);
        });

        // human going into elevator
        elevator.on(ElevatorEvent.ENTER, data -> {
            Human human = (Human)data;
            System.out.println(human.getName() + " entrou no elevador");
        });

        // human leaving elevator
        elevator.on(ElevatorEvent.LEAVE, data -> {
            Human human = (Human)data;
            System.out.println(human.getName() + " saiu do elevador");
        });
    }
}
