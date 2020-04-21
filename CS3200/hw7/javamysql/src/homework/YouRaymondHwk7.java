/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.

db.mysql.url="jdbc:mysql://localhost:3306/db?characterEncoding=UTF-8&useSSL=false"
*/
package homework;

import java.sql.CallableStatement;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.HashSet;
import java.util.Properties;
import java.util.Scanner;
import java.sql.ResultSet;


/**
 *
 * @author kath
 */
class JavaMySql {

  /** The name of the MySQL account to use (or empty for anonymous) */
  //private final String userName = "root";

  /** The password for the MySQL account (or empty for anonymous) */
  //private final String password = "root";

  /** The name of the computer running MySQL */
  private final String serverName = "localhost";

  /** The port of the MySQL server (default is 3306) */
  private final int portNumber = 3306;

  /** The name of the database we are testing with (this default is installed with MySQL) */
  private final String dbName = "lotr";

  /** The name of the table we are testing with */
  private final String tableName = "lotrbooks";
  private final boolean useSSL = false;

  /**
   * Get a new database connection
   *
   * @return
   * @throws SQLException
   */
  public Connection getConnection() throws SQLException {
    //Question 1
    Scanner scan = new Scanner(System.in);
    System.out.print("Enter MySQL Account Username: ");
    String usernameInput = scan.nextLine();
    System.out.print("Enter MySQL Account Password: ");
    String passwordInput = scan.nextLine();


    Connection conn = null;
    Properties connectionProps = new Properties();
    connectionProps.put("user", usernameInput);
    connectionProps.put("password", passwordInput);

    conn = DriverManager.getConnection("jdbc:mysql://"
                    + this.serverName + ":" + this.portNumber + "/" + this.dbName + "?characterEncoding=UTF-8&useSSL=false",
            connectionProps);

    return conn;
  }

  /**
   * Run a SQL command which does not return a recordset:
   * CREATE/INSERT/UPDATE/DELETE/DROP/etc.
   *
   * @throws SQLException If something goes wrong
   */
  public boolean executeUpdate(Connection conn, String command) throws SQLException {
    Statement stmt = null;
    try {
      stmt = conn.createStatement();
      stmt.executeUpdate(command); // This will throw a SQLException if it fails
      return true;
    } finally {

      // This will run whether we throw an exception or not
      if (stmt != null) { stmt.close(); }
    }
  }

  /**
   * Connect to MySQL and do some stuff.
   */
  public void run() {

    // Connect to MySQL
    Connection conn = null;
    // Question 2
    try {
      conn = this.getConnection();
      System.out.println("Connected to database");
    } catch (SQLException e) {
      System.out.println("ERROR: Could not connect to the database");
      e.printStackTrace();
      return;
    }

    // Question 3 (just uncomment below. But same thing is being done for question 4 so I commented out here)
    //System.out.println("Enter a character name: ");
    //Scanner scan = new Scanner(System.in);
    //String characternameInput = scan.nextLine();

    // Question 4
    try {
      String query = "SELECT character_name FROM lotr_character";
      HashSet<String> listOfCharacters = new HashSet<>();
      ResultSet resultSet = null;
      Statement statement = conn.createStatement();
      resultSet = statement.executeQuery(query);
      while (resultSet.next()) {
        listOfCharacters.add(resultSet.getString(1));
      }
      System.out.print("The character names in table lotr_character are: ");
      for(String character: listOfCharacters) {
        System.out.print(character + " ");
      }
      System.out.println();
      System.out.print("Pick a character name from the list above: ");
      Scanner scan = new Scanner(System.in);

      //Question 7
      String characternameInput = "";
      while(characternameInput.equals("")) {
        String input = scan.nextLine();
        if(listOfCharacters.contains(input)) {
          characternameInput = input;
          break;
        }
        System.out.println("Please enter another character name. " + input + " doesn't exist.");
      }

      //Question 5
      String query2 = "{CALL track_character(?)}";
      ResultSet resultSet2 = null;
      CallableStatement stmt = conn.prepareCall(query2);
      stmt.setString(1, characternameInput);
      resultSet2 = stmt.executeQuery();

      //Question 6
      String encounteredNames = "";
      while (resultSet2.next()) {
        encounteredNames = resultSet2.getString(4);
      }
      String[] returnedNames = encounteredNames.split(", ");
      System.out.print("The characters that " + characternameInput + " has encountered are: ");
      for(int i = 0; i < returnedNames.length; i++) {
        System.out.print(returnedNames[i] + " ");
      }
      System.out.println();


    } catch (SQLException e) {
      e.printStackTrace();
    }

    //Question 8
    try {
      conn.close();
      System.exit(0);
    } catch (SQLException e) {
      e.printStackTrace();
    }
  }



  /**
   * Connect to the DB and do some stuff
   * @param args
   */
  public static void main(String[] args) {
    JavaMySql app = new JavaMySql();
    app.run();
  }
}




