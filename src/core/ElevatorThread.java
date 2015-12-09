package core;

import util.Log;

/**
 * Comportamento da thread principal do elevador
 */
public class ElevatorThread implements Runnable{
    public static int TIME_INTERVAL = 1000;

    private /*@ spec_public non_null @*/ Elevator elevator;
    private /*@ spec_public non_null @*/ ElevatorStatus status;
    
    public ElevatorThread(Elevator elev) {
        elevator = elev;
        status = elev.status;
    }

    @Override
    public void run() {
        while(true){
            // Se alcancou o piso de destino, abrir a porta
            if(status.isMoving() && status.getCurrentFloor() == status.getTargetFloor()){
                status.setOpen(true);
                status.setMoving(false);
                elevator.emit(ElevatorEvent.OPEN, status.getCurrentFloor());
            }
            // fechado
            else if(status.isOpen()){
                status.setOpen(false);
                elevator.emit(ElevatorEvent.CLOSE, status.getCurrentFloor());
            }
            // Se nao alcancou o piso de destino, continuar em movimento
            else if(status.getTargetFloor() != 0 && status.getCurrentFloor() != status.getTargetFloor()){
                if(status.getCurrentFloor() < status.getTargetFloor()) moveFloor(status, true);
                else moveFloor(status, false);

                status.setMoving(true);

                elevator.emit(ElevatorEvent.MOVING, status.getCurrentFloor());
            }
            // em espera
            else{
                elevator.emit(ElevatorEvent.PENDING);
            }

            try {
                Thread.sleep(TIME_INTERVAL);
            } catch (InterruptedException e) {
                Log.error("Thread principal do elevador interrompida", e);
                break;
            }
        }
    }

    /**
     * Piso do elevador em movimento
     * @param status Objeto de estado do elevador
     * @param isIncrease Direcao do movimento
     */
    private void moveFloor(ElevatorStatus status, boolean isIncrease){
        if(isIncrease){
            status.setCurrentFloor(status.getCurrentFloor() + 1);
            if(status.getCurrentFloor() == 0)
                status.setCurrentFloor(status.getCurrentFloor() + 1);
        } else {
            status.setCurrentFloor(status.getCurrentFloor() - 1);
            if(status.getCurrentFloor() == 0)
                status.setCurrentFloor(status.getCurrentFloor() - 1);
        }
    }
}
