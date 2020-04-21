package WardrobeApp;


import java.util.Scanner;

public class Main {

  public static void main(String[] args) {
    Model model = new Model();
    boolean connected = false;
    Scanner scan = new Scanner(System.in);
    boolean mainMenu = true;
    boolean mainMenu2 = false;
    boolean outfitMenu;
    boolean articleMenu;
    boolean outfitArticleMenu;
    boolean loggedIn = false;
    boolean usernameTaken = false;
    boolean searchMenu;
    Integer integerInput;
    String stringInput;
    User user = null;

    //connect to database
    while (!connected) {
      System.out.print("Enter MySQL Account Username: ");
      String usernameInput = scan.nextLine();
      System.out.print("Enter MySQL Account Password: ");
      String passwordInput = scan.nextLine();
      System.out.print("Enter Database Name: ");
      String databaseInput = scan.nextLine();
      model.connect(usernameInput, passwordInput, databaseInput);
      if (model.getConnection() != null) {
        connected = true;
      } else {
        System.out.println("Try again");
      }
    }
    System.out.println();
    

    //main menu after connecting to db
    while (mainMenu) {
      //log in, register, or exit program
      while (!loggedIn) {
        printBorder();
        System.out.println("1. Log In");
        System.out.println("2. Register");
        System.out.println("3. Exit Program");
        printBorder();
        integerInput = scan.nextInt();
        scan.nextLine();
        //log in
        if (integerInput == 1) {
          printBorder();
          System.out.println("Logging in...");
          System.out.print("Enter username: ");
          String username = scan.nextLine();
          System.out.print("Enter password: ");
          String password = scan.nextLine();
          try {
            model.login(username, password);
            user = new User(model.getUserID(), model.getConnection());
          } catch (Exception e) {
            System.out.println(e.getMessage());
          }
          if (model.getLogin() == null) {
            System.out.println("Wrong username or password");
          } else {
            loggedIn = true;
            mainMenu2 = true;
          }
        }
        //register
        else if (integerInput == 2) {
          while(!usernameTaken) {
            printBorder();
            System.out.println("Registering...");
            System.out.print("Enter your first name: ");
            String firstName = scan.nextLine();
            System.out.print("Enter your last name: ");
            String lastName = scan.nextLine();
            System.out.print("Enter your age: ");
            int age = scan.nextInt();
            scan.nextLine();
            System.out.print("Enter your gender (Male, Female): ");
            String gender = scan.nextLine();
            System.out.print("Enter your email address: ");
            String emailAddress = scan.nextLine();
            System.out.print("Enter a username: ");
            String username = scan.nextLine();
            System.out.print("Enter a password: ");
            String password = scan.nextLine();
            if(model.checkIfUsernameExists(username)) {
              System.out.println("Username has already been taken.");
              System.out.println("Please try again!");
            }
            else {
              model.registerAccount(firstName, lastName, age, gender, emailAddress, username, password);
              System.out.println("Successfully registered account. Now log in!");
              usernameTaken = true;
            }
          }
        }
        //exit program
        else if (integerInput == 3) {
          printBorder();
          System.out.println("Exiting program...");
          mainMenu = false;
          break;
        } else {
          printBorder();
          System.out.println("Please enter a valid integer input. Try again.");
        }
      }
      //main menu where you actually perform CRUD and other operations
      while (mainMenu2) {
        printBorder();
        System.out.println("1. Create, read, update, or delete an outfit");
        System.out.println("2. Create, read, update, or delete an article");
        System.out.println("3. Add, remove, update, or view articles in an outfit");
        System.out.println("4. Search for articles");
        System.out.println("5. View account info");
        System.out.println("6. Log Out");
        printBorder();
        integerInput = scan.nextInt();
        scan.nextLine();
        //1. Create, read, update, or delete an outfit
        if (integerInput == 1) {
          outfitMenu = true;
          while (outfitMenu) {
            printBorder();
            System.out.println("1. Create an outfit");
            System.out.println("2. View outfits");
            System.out.println("3. Update an outfit");
            System.out.println("4. Delete an outfit");
            System.out.println("5. Go Back to main menu");
            printBorder();
            integerInput = scan.nextInt();
            scan.nextLine();
            // 1. create an outfit
            if (integerInput == 1) {
              printBorder();
              System.out.println("Creating an outfit...");
              System.out.print("Enter a description for the outfit: ");
              stringInput = scan.nextLine();
              model.addOutfit(stringInput);

            }
            // 2. view outfits
            else if (integerInput == 2) {
              //check if there are outfits
              if (user.getNumberOfOutfits() == 0) {
                printBorder();
                System.out.println("You have no outfits");
              } else {
                printBorder();
                user.printOutfits();
              }
            }
            //3. update an outfit
            else if (integerInput == 3) {
              //check if there are outfits
              if (user.getNumberOfOutfits() == 0) {
                printBorder();
                System.out.println("You have no outfits");
              } else {
                printBorder();
                System.out.println("Here are all your outfits.");
                user.printOutfits();
                printBorder();
                System.out.print("Enter the outfitID of the outfit you want you to update: ");
                integerInput = scan.nextInt();
                scan.nextLine();
                //check if the input is actually an outfit ID
                if (user.hasOutfitID(integerInput)) {
                  System.out.print("Update new outfit description for outfit with ID " + integerInput + ": ");
                  stringInput = scan.nextLine();
                  Outfit temp = new Outfit(integerInput, model.getConnection());
                  temp.updateDescription(stringInput);
                } else {
                  System.out.println("An outfit with that outfitID doesn't exist.");
                }
              }
            }
            //4. delete an outfit
            else if (integerInput == 4) {
              //check if there are outfits
              if (user.getNumberOfOutfits() == 0) {
                printBorder();
                System.out.println("You have no outfits");
              } else {
                printBorder();
                System.out.println("Here are all your outfits.");
                user.printOutfits();
                printBorder();
                System.out.print("Enter the outfitID of the outfit you want to delete: ");
                integerInput = scan.nextInt();
                scan.nextLine();
                //check if the input is actually an outfit ID
                if (user.hasOutfitID(integerInput)) {
                  Outfit temp = new Outfit(integerInput, model.getConnection());
                  temp.deleteOutfit(integerInput);
                } else {
                  printBorder();
                  System.out.println("An outfit with that outfitID doesn't exist.");
                }
              }
            }
            //go back to main menu
            else if (integerInput == 5) {
              outfitMenu = false;
            }
            //invalid input
            else {
              printBorder();
              System.out.println("Please enter a valid integer input. Try again.");
            }
          }
        }

        //2. Create, read, update, or delete an article
        else if (integerInput == 2) {
          articleMenu = true;
          while (articleMenu) {
            printBorder();
            System.out.println("1. Create an article");
            System.out.println("2. View an article");
            System.out.println("3. Update an article");
            System.out.println("4. Delete an article");
            System.out.println("5. Go Back to main menu");
            printBorder();
            integerInput = scan.nextInt();
            scan.nextLine();
            //1. create an article
            if (integerInput == 1) {
              printBorder();
              System.out.print("Enter the type of article (short-sleeve, long-sleeve, hoodie, etc): ");
              String type = scan.nextLine();
              String typeDescription = "a " + type + " article";
              System.out.print("Enter the size of the article (small, medium, large, etc): ");
              String size = scan.nextLine();
              System.out.print("Enter the color of the article (red, yellow, blue, etc): ");
              String color = scan.nextLine();
              System.out.print("Enter the brand of the article (Uniqlo, Express, Abercrombie, etc): ");
              String brand = scan.nextLine();
              System.out.print("Enter the material/fabric of the article (cotton, polyester, nylon, etc): ");
              String material = scan.nextLine();
              System.out.print("Enter the cost/price of the article (10, 20, 30, 100, etc): ");
              int price = scan.nextInt();
              scan.nextLine();
              System.out.print("Enter a description for the article (streetwear, for date nights, match with yellow top, etc): ");
              String description = scan.nextLine();
              System.out.print("Enter the date of purchase the article in this format (YYYY-MM-DD): ");
              String date = scan.nextLine();
              //check if type is already in table as no need to create duplicate types
              if(user.getTypeIDFromDescription(type) == 0) {
                model.addType(type, typeDescription);
                model.addArticle(model.getTypeID(), size, color, brand, material, price, description, date);
              }
              //type doesn't exist
              else {
                int tempType = user.getTypeIDFromDescription(type);
                model.addArticle(tempType, size, color, brand, material, price, description, date);
              }
            }
            //2. view an article
            else if (integerInput == 2) {
              //check if there are any articles
              if (user.getNumberOfArticles() == 0) {
                printBorder();
                System.out.println("You have no articles");
              } else {
                printBorder();
                user.printArticles();
              }
            }
            //3. update an article
            else if (integerInput == 3) {
              //check if there are any articles
              if (user.getNumberOfArticles() == 0) {
                printBorder();
                System.out.println("You have no articles");
              } else {
                printBorder();
                System.out.println("Here are all your articles.");
                user.printArticles();
                printBorder();
                System.out.print("Enter the articleID of the article you want you to update: ");
                integerInput = scan.nextInt();
                scan.nextLine();
                //check if input is actually an articleID
                if (user.hasArticleID(integerInput)) {
                  printBorder();
                  Article temp = new Article(integerInput, model.getConnection());
                  System.out.print("Update the type of article (short-sleeve, long-sleeve, hoodie, etc): ");
                  String type = scan.nextLine();
                  System.out.print("Update the size of the article (small, medium, large, etc): ");
                  String size = scan.nextLine();
                  System.out.print("Update the color of the article (red, yellow, blue, etc): ");
                  String color = scan.nextLine();
                  System.out.print("Update the brand of the article (Uniqlo, Express, Abercrombie, etc): ");
                  String brand = scan.nextLine();
                  System.out.print("Update the material/fabric of the article (cotton, polyester, nylon, etc): ");
                  String material = scan.nextLine();
                  System.out.print("Update the cost/price of the article (10, 20, 30, 100, etc): ");
                  int price = scan.nextInt();
                  scan.nextLine();
                  System.out.print("Update description for the article (streetwear, for date nights, match with yellow top, etc): ");
                  String description = scan.nextLine();
                  System.out.print("Update the date of purchase of the article in this format (YYYY-MM-DD): ");
                  String date = scan.nextLine();
                  temp.updateQualities(type, size, color, brand, material, price, description, date);
                } else {
                  printBorder();
                  System.out.println("An article with that articleID doesn't exist.");
                }
              }
            }
            //4. delete an article
            else if (integerInput == 4) {
              //check if there are any articles
              if (user.getNumberOfArticles() == 0) {
                printBorder();
                System.out.println("You have no articles");
              } else {
                printBorder();
                System.out.println("Here are all your articles.");
                user.printArticles();
                printBorder();
                System.out.print("Enter the articleID of the article you want you to delete: ");
                integerInput = scan.nextInt();
                scan.nextLine();
                //check if input is actually an articleID
                if (user.hasArticleID(integerInput)) {
                  Article temp = new Article(integerInput, model.getConnection());
                  temp.deleteArticle(integerInput);
                } else {
                  printBorder();
                  System.out.println("An article with that articleID doesn't exist.");
                }
              }
            }
            //5. go back to main menu
            else if (integerInput == 5) {
              articleMenu = false;
            }
            //invalid input
            else {
              printBorder();
              System.out.println("Please enter a valid integer input. Try again.");
            }
          }

        }
        //3. Add, remove, update, or view articles in an outfit
        else if (integerInput == 3) {
          outfitArticleMenu = true;
          while (outfitArticleMenu) {
            if(user.getNumberOfArticles() == 0) {
              printBorder();
              System.out.println("You have no articles");
              break;
            }
            if (user.getNumberOfOutfits() == 0) {
              printBorder();
              System.out.println("You have no outfits");
              break;
            } else {
              printBorder();
              System.out.println("Here are your outfits");
              user.printOutfits();
              printBorder();
              System.out.print("Enter the outfit ID of the outfit you want to modify or 0 to go back to the main menu: ");
              integerInput = scan.nextInt();
              scan.nextLine();
              //check if input is an actual outfitID
              if (user.hasOutfitID(integerInput)) {
                printBorder();
                System.out.println("You are now modifying outfit ID: " + integerInput);
                Outfit temp = new Outfit(integerInput, model.getConnection());
                System.out.println("1. Add an article to this outfit");
                System.out.println("2. Remove an article from this outfit");
                System.out.println("3. View articles from this outfit");
                System.out.println("4. Go back to the main menu");
                printBorder();
                integerInput = scan.nextInt();
                scan.nextLine();
                //1. add an article to this outfit
                if (integerInput == 1) {
                  if (temp.getNumberOfArticles() != 0) {
                    printBorder();
                    System.out.println("Here are your current articles in outfit " + temp.getOutfitID() + " with description \"" + temp.getDescription() + "\"");
                    temp.printDescriptionOfAllArticles();
                    printBorder();
                    //fix to print articles not in the outfit
                    System.out.println("Here are your articles not in this outfit (which you can add)");
                    temp.printDescriptionOfAllArticlesNotInOutfit();
                    printBorder();
                    System.out.print("Enter the article IDs (with a space between) of the articles you wish to add to this outfit: ");
                    String[] strArray = scan.nextLine().split(" ");
                    for (int i = 0; i < strArray.length; i++) {
                      model.addArticleToOutfit(Integer.parseInt(strArray[i]), temp.getOutfitID());
                    }
                    printBorder();
                    System.out.println("Here are your current articles after the additions in outfit " + temp.getOutfitID() + " with description \"" + temp.getDescription() + "\"");
                    temp.printDescriptionOfAllArticles();
                    printBorder();
                    outfitArticleMenu = false;
                  } else {
                    System.out.println("You currently have 0 articles in outfit " + temp.getOutfitID() + " with description \"" + temp.getDescription() + "\"");
                    printBorder();
                    System.out.println("Here are your articles which you can add to this outfit");
                    user.printArticles();
                    printBorder();
                    System.out.print("Enter the article IDs (with a space between) of the articles you wish to add to this outfit: ");
                    String[] strArray = scan.nextLine().split(" ");
                    for (int i = 0; i < strArray.length; i++) {
                      model.addArticleToOutfit(Integer.parseInt(strArray[i]), temp.getOutfitID());
                    }
                    printBorder();
                    System.out.println("Here are your current articles after the additions in outfit " + temp.getOutfitID() + " with description \"" + temp.getDescription() + "\"");
                    temp.printDescriptionOfAllArticles();
                    outfitArticleMenu = false;
                  }
                }
                //2. Remove an article from this outfit
                else if (integerInput == 2) {
                  if (temp.getNumberOfArticles() != 0) {
                    printBorder();
                    System.out.println("Here are your current articles in outfit " + temp.getOutfitID() + " with description \"" + temp.getDescription() + "\"");
                    temp.printDescriptionOfAllArticles();
                    printBorder();
                    System.out.print("Enter the article IDs (with a space between) of the articles you wish to remove from this outfit: ");
                    String[] strArray = scan.nextLine().split(" ");
                    for (int i = 0; i < strArray.length; i++) {
                      model.removeArticleToOutfit(Integer.parseInt(strArray[i]), temp.getOutfitID());
                    }
                    printBorder();
                    System.out.println("Here are your current articles after the deletions in outfit " + temp.getOutfitID() + " with description \"" + temp.getDescription() + "\"");
                    temp.printDescriptionOfAllArticles();
                    outfitArticleMenu = false;
                  } else {
                    printBorder();
                    System.out.println("Here are your current articles in this outfit");
                    System.out.println("You currently have zero articles in this outfit to remove");
                    outfitArticleMenu = false;
                  }
                }
                //3. View articles from this outfit
                else if (integerInput == 3) {
                  if (temp.getNumberOfArticles() != 0) {
                    printBorder();
                    System.out.println("Here are your current articles in outfit " + temp.getOutfitID() + " with description \"" + temp.getDescription() + "\"");
                    temp.printDescriptionOfAllArticles();
                    outfitArticleMenu = false;
                  } else {
                    printBorder();
                    System.out.println("Here are your current articles in this outfit:");
                    System.out.println("You currently have zero articles in this outfit to view");
                    outfitArticleMenu = false;
                  }
                }
                //4. Go back to the main menu
                else if (integerInput == 4) {
                  printBorder();
                  outfitArticleMenu = false;
                }
                //invalid input
                else {
                  printBorder();
                  System.out.println("Please enter a valid integer input. Try again.");
                }
              }
              //0. go back to the main menu
              else if (integerInput == 0) {
                outfitArticleMenu = false;
              }
              //invalid outfit ID
              else {
                printBorder();
                System.out.println("Please enter a valid outfit ID.");
              }
            }

          }

        }
        //4. Search for articles
        else if (integerInput == 4) {
          searchMenu = true;
          while(searchMenu) {
            printBorder();
            System.out.println("1. Search by article type");
            System.out.println("2. Search by size");
            System.out.println("3. Search by color");
            System.out.println("4. Search by brand");
            System.out.println("5. Search by material");
            System.out.println("6. Search by price range");
            System.out.println("7. Go back to main menu");
            integerInput = scan.nextInt();
            scan.nextLine();
            printBorder();
            //1. search by article type
            if(integerInput == 1) {
              System.out.print("Please enter the article type: ");
              stringInput = scan.nextLine();
              printBorder();
              user.searchWithColumnAndValueType(stringInput);
            }
            //2. search by size
            else if(integerInput == 2) {
              System.out.print("Please enter the article size: ");
              stringInput = scan.nextLine();
              printBorder();
              user.searchWithColumnAndValueString("Size", stringInput);
            }
            //3. search by color
            else if(integerInput == 3) {
              System.out.print("Please enter the article color: ");
              stringInput = scan.nextLine();
              printBorder();
              user.searchWithColumnAndValueString("Color", stringInput);
            }
            //4. search by brand
            else if(integerInput == 4) {
              System.out.print("Please enter the article brand: ");
              stringInput = scan.nextLine();
              printBorder();
              user.searchWithColumnAndValueString("Brand", stringInput);
            }
            //5. search by material
            else if(integerInput == 5) {
              System.out.print("Please enter the article material: ");
              stringInput = scan.nextLine();
              printBorder();
              user.searchWithColumnAndValueString("Material", stringInput);
            }
            //6. search by price range
            else if(integerInput == 6) {
              System.out.print("Please enter the lower bound for price range: ");
              int lowerBound = scan.nextInt();
              scan.nextLine();
              System.out.print("Please enter the upper bound for price range: ");
              int upperBound = scan.nextInt();
              scan.nextLine();
              printBorder();
              user.searchWithLowerAndUpper(lowerBound, upperBound);
            }
            //go back to main menu
            else if(integerInput == 7) {
              break;
            }
            //invalid input
            else {
              printBorder();
              System.out.println("Please enter a valid integer input");
            }

          }

        }
        //5. Get account info
        else if (integerInput == 5) {
          user.printUserInformation();

        }
        //6. log out
        else if (integerInput == 6) {
          printBorder();
          System.out.println("Logging out...");
          model.logout();
          mainMenu2 = false;
          loggedIn = false;
        }
        //invalid input
        else {
          printBorder();
          System.out.println("Please enter a valid integer input. Try again.");
        }
      }
    }
    model.close();
  }

  //method to print border to make it look nice
  public static void printBorder() {
    System.out.println("===================================================================================================================================" +
            "===========================================================================================================================");
  }
}
