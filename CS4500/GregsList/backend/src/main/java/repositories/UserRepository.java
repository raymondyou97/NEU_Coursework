package repositories;

import models.FrequentlyAskedAnswer;
import models.Service;
import models.ServiceAnswer;
import java.util.List;

import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;

import models.User;

public interface UserRepository extends CrudRepository<User, Integer> {
    @Query(value = "SELECT user FROM User user")
    public List<User> findAllUsers();

    @Query(value = "SELECT user FROM User user WHERE user.id=:id")
    public User findUserById(@Param("id") Integer id);

    @Query(value = "SELECT user FROM User user WHERE user.username=:username")
    public User findByUsername(@Param("username") String username);

    @Query(value = "SELECT serviceAnswers FROM User user WHERE user.id=:id")
    public List<ServiceAnswer> findAllServiceAnswersForUser(@Param("id") Integer id);

    @Query(value = "SELECT frequentlyAskedAnswers from FrequentlyAskedAnswer frequentlyAskedAnswers WHERE frequentlyAskedAnswers.user.id=:id")
    public List<FrequentlyAskedAnswer> findAllFrequentlyAskedAnswersForUser(@Param("id") Integer id);

    @Query(value = "SELECT services from User user WHERE user.id=:id")
    public List<Service> findAllServicesForUser(@Param("id") Integer id);
    // @Query(value="SELECT reviewed FROM User user WHERE user.id=:id")
    // public List<Review> findAllReviewsOfUserForUser(@Param("id") Integer id);
    // @Query(value="SELECT reviewer FROM User user WHERE user.id=:id")
    // public List<Review> finadAllReviewsOfOthersForUser(@Param("id") Integer id);
}