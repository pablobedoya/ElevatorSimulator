package main;
import core.Elevator;
import core.Human;
import util.Watcher;

public class Main {
    public static void main(String[] args) {
        Elevator elevator = new Elevator();

        Watcher watcher = new Watcher();
        watcher.watch(elevator);

        elevator.launch();

        new Human()
                .setName("Tom")
                .setElevator(elevator)
                .setCurrentFloor(3)
                .setTargetFloor(8).go();

        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        new Human()
                .setName("Rachel")
                .setElevator(elevator)
                .setCurrentFloor(5)
                .setTargetFloor(1).go();
    }
}