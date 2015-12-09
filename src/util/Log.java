package util;

import java.util.logging.Logger;

/**
 * Log
 */
public class Log {
    private static Logger logger = Logger.getLogger("logger");

    /*@	requires msg.equals("") && msg != null; @*/
    public /*@ pure @*/ static void info(String msg){
        logger.info(msg);
    }

    /*@	requires msg.equals("") && msg != null; @*/
    public /*@ pure @*/ static void error(String msg, Exception e) {
        logger.severe(msg);
        e.printStackTrace();
    }
}
