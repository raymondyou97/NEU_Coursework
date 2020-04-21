package repositories;

import models.ServiceAnswer;
import models.ServiceQuestion;
import models.User;
import java.util.List;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;

public interface ServiceAnswerRepository extends CrudRepository<ServiceAnswer, Integer> {
    @Query(value = "SELECT serviceAnswer FROM ServiceAnswer serviceAnswer WHERE serviceAnswer.id=:id")
    ServiceAnswer findServiceAnswerById(@Param("id") Integer id);

    @Query(value = "SELECT serviceAnswer FROM ServiceAnswer serviceAnswer")
    List<ServiceAnswer> getAllServiceAnswers();

    @Query(value = "SELECT serviceAnswer FROM ServiceAnswer serviceAnswer "
            + "WHERE serviceAnswer.provider.id=:providerId")
    List<ServiceAnswer> findAllServiceAnswersForProvider(@Param("providerId") Integer providerId);

    @Query(value = "SELECT provider FROM ServiceAnswer serviceAnswer WHERE serviceAnswer.id=:id")
    User findProviderForServiceAnswer(Integer id);

    @Query(value = "SELECT serviceAnswer FROM ServiceAnswer serviceAnswer "
            + "WHERE serviceAnswer.serviceQuestion.id=:serviceQuestionId")
    List<ServiceAnswer> findAllServiceAnswersForServiceQuestion(@Param("serviceQuestionId") Integer serviceQuestionId);

    @Query(value = "SELECT serviceQuestion FROM ServiceAnswer serviceAnswer "
            + "WHERE serviceAnswer.id=:serviceAnswerId")
    ServiceQuestion findServiceQuestionForServiceAnswer(@Param("serviceAnswerId") Integer serviceAnswerId);
}
