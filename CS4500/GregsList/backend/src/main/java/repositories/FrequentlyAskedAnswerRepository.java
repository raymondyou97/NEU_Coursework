package repositories;

import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;

import java.util.List;

import models.FrequentlyAskedAnswer;

public interface FrequentlyAskedAnswerRepository extends CrudRepository<FrequentlyAskedAnswer, Integer> {

    @Query(value = "SELECT faa FROM FrequentlyAskedAnswer faa WHERE faa.id=:id")
    FrequentlyAskedAnswer findFrequentlyAskedAnswerById(@Param("id") Integer id);

    @Query(value = "SELECT faa FROM FrequentlyAskedAnswer faa")
    List<FrequentlyAskedAnswer> getAllFrequentlyAskedAnswers();

    @Query(value = "SELECT faa FROM FrequentlyAskedAnswer faa WHERE faa.user.id=:userId")
    List<FrequentlyAskedAnswer> findAllFrequentlyAskedAnswersForProvider(@Param("userId") Integer providerId);

    @Query(value = "SELECT faa FROM FrequentlyAskedAnswer faa WHERE faa" + ".frequentlyAskedQuestion.id=:faqId")
    List<FrequentlyAskedAnswer> findAllFrequentlyAskedAnswersForFrequentlyAskedQuestion(@Param("faqId") Integer faqId);
}
