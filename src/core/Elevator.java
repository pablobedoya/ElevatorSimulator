package core;

import event.Callback;
import event.EventEmitter;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Classe Elevator
 */
public class Elevator extends EventEmitter{
    // Lista de pedidos de elevador
    private List<Request> requests = new LinkedList<Request>();
    // Estado do elevador
    ElevatorStatus status = new ElevatorStatus();

    /**
     * Elevador partindo
     */
    public void launch() {
        // Iniciando a thread principal
        new Thread(new ElevatorThread(this)).start();
        this.emit(ElevatorEvent.LAUNCH, status.currentFloor);

        // Removendo todas as solicitações que já chegaram
        this.on(ElevatorEvent.OPEN, data -> {
            int currentFloor = (Integer) data;
            requests = requests.stream().filter((req) -> !(req.stopFloor == currentFloor))
                    .collect(Collectors.toList());
        });

        // Elevador fechado, executando próximo pedido
        this.on(ElevatorEvent.CLOSE, data -> updateTarget());
    }

    /**
     * Botão externo do elevador é pressionado
     * @param direction Diereção
     * @param currentFloor Piso atual
     * @param presser Pessoa que pressionou o botão
     * @return Elevator
     */
    public Elevator outerPress(Direction direction, int currentFloor, Human presser) {
        // Configurando solicitações de botões externos para adicinoar à lista de solicitações
        OuterRequest req = new OuterRequest()
                .setDirection(direction)
                .setCurrentFloor(currentFloor)
                .setPresser(presser);
        requests.add(req);

        // Evento disparador
        this.emit(ElevatorEvent.OUTER_PRESSED, req);
        updateTarget();

        return this;
    }

    /**
     * Botão interno do elevador é pressionado
     * @param targetFloor Piso de destino
     * @param presser Pessoa que pressionou o botão
     * @return Elevator
     */
    public Elevator innerPress(int targetFloor, Human presser) {
    	// Configurando solicitações de botões externos para adicinoar à lista de solicitações
        InnerRequest req = new InnerRequest()
                .setCurrentFloor(status.currentFloor)
                .setTargetFloor(targetFloor)
                .setPresser(presser);
        requests.add(req);

        // Evento disparador
        this.emit(ElevatorEvent.INNER_PRESSED, req);
        updateTarget();

        return this;
    }

    /**
     * Atualizar piso do elevador em movimento
     * Disparo indireto, elevador em movimento
     */
    private void updateTarget(){
        // Primeira solicitação a ser processada, depois de passar um valor específico
        Request first;
        // A lista de solicitações é ordenada, se o elevador está indo para cima, em seguida,
        // pela ordem inversa de acordo com a altura do piso, prioriza o piso mais alto e vice-versa
        sort(requests);
        if(requests.size() == 0) return;

        first = requests.get(0);
        // Estabelecer um piso de destino
        status.targetFloor = first.getStopFloor();
    }

    /**
     * Todos as solicitações são classificadas de acordo com a prioridade
     * @param requests Solicitação
     */
    private void sort(List<Request> requests){
        // O piso atual do elevador
        int currentFloor = status.currentFloor;
        Direction currentDirection = status.direction;

        // Para subir, por exemplo, todos as solicitações são divididas nas seguintes categorias:
        // 1. Se a solicitação é maior do que o piso atual do elevador
        // 2. Solicitação para descer
        // 3. Solicitação é menor do que o piso atual com elevador
        // Caso contrário, o elevador desce

        // O primeiro tipo de solicitação
        List<Request> list1 = requests.stream().filter( req -> {
            // Se na mesma direção
            boolean isSame = req.getDirection() == currentDirection;
            // É prioridade
            boolean isSuper = (currentDirection == Direction.UP)?
                    (req.getStopFloor() >= currentFloor)
                    :(req.getStopFloor() < currentFloor);

            return isSame && isSuper;
        }).sorted( (lhs,rhs) -> {
        	// No primeiro tipo, subir é a menor prioridade
            if(currentDirection == Direction.UP){
                return lhs.getStopFloor() - rhs.getStopFloor();
            }else{
                return -(lhs.getStopFloor() - rhs.getStopFloor());
            }
        }).collect(Collectors.toList());

        // O segundo tipo de solicitação
        List<Request> list2 = requests.stream().filter( req -> {
            // Se na direção reversa
            boolean isSame = (req.getDirection() == currentDirection);
            return !isSame;
        }).sorted( (lhs,rhs) -> {
            // No segundo tipo, subir é a maior prioridade
            if(currentDirection == Direction.UP){
                return -(lhs.getStopFloor() - rhs.getStopFloor());
            }else{
                return lhs.getStopFloor() - rhs.getStopFloor();
            }
        }).collect(Collectors.toList());


        // O terceiro tipo de solicitação
        List<Request> list3 = requests.stream().filter( req -> {
            // Se na mesma direção
            boolean isSame = req.getDirection() == currentDirection;
            // É prioridade
            boolean isSuper = (currentDirection == Direction.UP)?
                    (req.getStopFloor() >= currentFloor)
                    :(req.getStopFloor() < currentFloor);

            return isSame && !isSuper;
        }).sorted( (lhs,rhs) -> {
            // No terceiro tipo, subir é a maior prioridade
            if(currentDirection == Direction.UP){
                return lhs.getStopFloor() - rhs.getStopFloor();
            }else{
                return -(lhs.getStopFloor() - rhs.getStopFloor());
            }
        }).collect(Collectors.toList());

        requests.clear();

        // Uma combinação de três tipos de solicitação
        requests.addAll(list1);
        requests.addAll(list2);
        requests.addAll(list3);
    }

    // Substituir o método da classe pai
    public <T> void emit(ElevatorEvent type, T... data) {
        super.emit(type, data);
    }
    // Substituir o método da classe pai
    public void on(ElevatorEvent type, Callback callback) {
        super.on(type, callback);
    }
}
