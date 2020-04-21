package repositories;

import models.ServiceCategory;
import models.ServiceQuestion;
import java.util.List;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;

public interface ServiceQuestionRepository extends CrudRepository<ServiceQuestion, Integer> {
    @Query(value = "SELECT serviceQuestion FROM ServiceQuestion serviceQuestion " + "WHERE serviceQuestion.id=:id")
    ServiceQuestion findServiceQuestionById(@Param("id") Integer id);

    @Query(value = "SELECT serviceQuestion FROM ServiceQuestion serviceQuestion")
    List<ServiceQuestion> getAllServiceQuestions();

    @Query(value = "SELECT serviceQuestion FROM ServiceQuestion serviceQuestion " + "WHERE serviceQuestion.type=:type")
    List<ServiceQuestion> findAllServiceQuestionsForType(@Param("type") String type);

    @Query(value = "SELECT serviceQuestion FROM ServiceQuestion serviceQuestion "
            + "WHERE serviceQuestion.service.id=:serviceId")
    List<ServiceQuestion> findAllServiceQuestionsForService(@Param("serviceId") Integer serviceId);

    @Query(value = "SELECT service FROM ServiceQuestion serviceQuestion " + "WHERE serviceQuestion.id=:id")
    ServiceCategory findServiceForServiceQuestion(@Param("id") Integer id);
}
